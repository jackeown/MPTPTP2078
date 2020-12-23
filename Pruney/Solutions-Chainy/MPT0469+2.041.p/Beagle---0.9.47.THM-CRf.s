%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:57 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   52 (  77 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  95 expanded)
%              Number of equality atoms :   21 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_8 > #skF_7 > #skF_2 > #skF_5 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_67,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_32,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_50,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_247,plain,(
    ! [A_80,B_81] :
      ( r2_hidden(k4_tarski('#skF_4'(A_80,B_81),'#skF_5'(A_80,B_81)),A_80)
      | r2_hidden('#skF_6'(A_80,B_81),B_81)
      | k1_relat_1(A_80) = B_81 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [B_55,A_56] :
      ( ~ r2_hidden(B_55,A_56)
      | k4_xboole_0(A_56,k1_tarski(B_55)) != A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    ! [B_55] : ~ r2_hidden(B_55,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_61])).

tff(c_1350,plain,(
    ! [B_119] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_119),B_119)
      | k1_relat_1(k1_xboole_0) = B_119 ) ),
    inference(resolution,[status(thm)],[c_247,c_66])).

tff(c_1474,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1350,c_66])).

tff(c_1509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1474])).

tff(c_1510,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1511,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1979,plain,(
    ! [A_163,B_164] :
      ( r2_hidden(k4_tarski('#skF_4'(A_163,B_164),'#skF_5'(A_163,B_164)),A_163)
      | r2_hidden('#skF_6'(A_163,B_164),B_164)
      | k1_relat_1(A_163) = B_164 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1526,plain,(
    ! [B_125,A_126] :
      ( ~ r2_hidden(B_125,A_126)
      | k4_xboole_0(A_126,k1_tarski(B_125)) != A_126 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1531,plain,(
    ! [B_125] : ~ r2_hidden(B_125,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1526])).

tff(c_2062,plain,(
    ! [B_164] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_164),B_164)
      | k1_relat_1(k1_xboole_0) = B_164 ) ),
    inference(resolution,[status(thm)],[c_1979,c_1531])).

tff(c_2085,plain,(
    ! [B_165] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_165),B_165)
      | k1_xboole_0 = B_165 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1511,c_2062])).

tff(c_16,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_1'(A_7),A_7)
      | v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1555,plain,(
    ! [B_129] : ~ r2_hidden(B_129,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1526])).

tff(c_1560,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_1555])).

tff(c_1562,plain,(
    ! [A_133,B_134] :
      ( r2_hidden('#skF_8'(A_133,B_134),k1_relat_1(B_134))
      | ~ r2_hidden(A_133,k2_relat_1(B_134))
      | ~ v1_relat_1(B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1565,plain,(
    ! [A_133] :
      ( r2_hidden('#skF_8'(A_133,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_133,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1511,c_1562])).

tff(c_1567,plain,(
    ! [A_133] :
      ( r2_hidden('#skF_8'(A_133,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_133,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1560,c_1565])).

tff(c_1568,plain,(
    ! [A_133] : ~ r2_hidden(A_133,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_1531,c_1567])).

tff(c_2161,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2085,c_1568])).

tff(c_2187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1510,c_2161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.60  
% 3.67/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.60  %$ r2_hidden > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_8 > #skF_7 > #skF_2 > #skF_5 > #skF_4
% 3.67/1.60  
% 3.67/1.60  %Foreground sorts:
% 3.67/1.60  
% 3.67/1.60  
% 3.67/1.60  %Background operators:
% 3.67/1.60  
% 3.67/1.60  
% 3.67/1.60  %Foreground operators:
% 3.67/1.60  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.67/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.67/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.67/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.67/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.67/1.60  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.67/1.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.67/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.67/1.60  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.67/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.67/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.67/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.67/1.60  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.67/1.60  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.67/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.67/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.67/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.67/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.67/1.60  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.67/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.67/1.60  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.67/1.60  
% 3.67/1.61  tff(f_67, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.67/1.61  tff(f_54, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.67/1.61  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.67/1.61  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.67/1.61  tff(f_46, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 3.67/1.61  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 3.67/1.61  tff(c_32, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.67/1.61  tff(c_50, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 3.67/1.61  tff(c_247, plain, (![A_80, B_81]: (r2_hidden(k4_tarski('#skF_4'(A_80, B_81), '#skF_5'(A_80, B_81)), A_80) | r2_hidden('#skF_6'(A_80, B_81), B_81) | k1_relat_1(A_80)=B_81)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.67/1.61  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.67/1.61  tff(c_61, plain, (![B_55, A_56]: (~r2_hidden(B_55, A_56) | k4_xboole_0(A_56, k1_tarski(B_55))!=A_56)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.67/1.61  tff(c_66, plain, (![B_55]: (~r2_hidden(B_55, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_61])).
% 3.67/1.61  tff(c_1350, plain, (![B_119]: (r2_hidden('#skF_6'(k1_xboole_0, B_119), B_119) | k1_relat_1(k1_xboole_0)=B_119)), inference(resolution, [status(thm)], [c_247, c_66])).
% 3.67/1.61  tff(c_1474, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1350, c_66])).
% 3.67/1.61  tff(c_1509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1474])).
% 3.67/1.61  tff(c_1510, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 3.67/1.61  tff(c_1511, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 3.67/1.61  tff(c_1979, plain, (![A_163, B_164]: (r2_hidden(k4_tarski('#skF_4'(A_163, B_164), '#skF_5'(A_163, B_164)), A_163) | r2_hidden('#skF_6'(A_163, B_164), B_164) | k1_relat_1(A_163)=B_164)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.67/1.61  tff(c_1526, plain, (![B_125, A_126]: (~r2_hidden(B_125, A_126) | k4_xboole_0(A_126, k1_tarski(B_125))!=A_126)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.67/1.61  tff(c_1531, plain, (![B_125]: (~r2_hidden(B_125, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1526])).
% 3.67/1.61  tff(c_2062, plain, (![B_164]: (r2_hidden('#skF_6'(k1_xboole_0, B_164), B_164) | k1_relat_1(k1_xboole_0)=B_164)), inference(resolution, [status(thm)], [c_1979, c_1531])).
% 3.67/1.61  tff(c_2085, plain, (![B_165]: (r2_hidden('#skF_6'(k1_xboole_0, B_165), B_165) | k1_xboole_0=B_165)), inference(demodulation, [status(thm), theory('equality')], [c_1511, c_2062])).
% 3.67/1.61  tff(c_16, plain, (![A_7]: (r2_hidden('#skF_1'(A_7), A_7) | v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.67/1.61  tff(c_1555, plain, (![B_129]: (~r2_hidden(B_129, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1526])).
% 3.67/1.61  tff(c_1560, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_1555])).
% 3.67/1.61  tff(c_1562, plain, (![A_133, B_134]: (r2_hidden('#skF_8'(A_133, B_134), k1_relat_1(B_134)) | ~r2_hidden(A_133, k2_relat_1(B_134)) | ~v1_relat_1(B_134))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.67/1.61  tff(c_1565, plain, (![A_133]: (r2_hidden('#skF_8'(A_133, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_133, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1511, c_1562])).
% 3.67/1.61  tff(c_1567, plain, (![A_133]: (r2_hidden('#skF_8'(A_133, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_133, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1560, c_1565])).
% 3.67/1.61  tff(c_1568, plain, (![A_133]: (~r2_hidden(A_133, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_1531, c_1567])).
% 3.67/1.61  tff(c_2161, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2085, c_1568])).
% 3.67/1.61  tff(c_2187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1510, c_2161])).
% 3.67/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.61  
% 3.67/1.61  Inference rules
% 3.67/1.61  ----------------------
% 3.67/1.61  #Ref     : 1
% 3.67/1.61  #Sup     : 409
% 3.67/1.61  #Fact    : 0
% 3.67/1.61  #Define  : 0
% 3.67/1.61  #Split   : 1
% 3.67/1.61  #Chain   : 0
% 3.67/1.61  #Close   : 0
% 3.67/1.61  
% 3.67/1.61  Ordering : KBO
% 3.67/1.61  
% 3.67/1.61  Simplification rules
% 3.67/1.61  ----------------------
% 3.67/1.61  #Subsume      : 82
% 3.67/1.61  #Demod        : 29
% 3.67/1.61  #Tautology    : 27
% 3.67/1.61  #SimpNegUnit  : 6
% 3.67/1.61  #BackRed      : 0
% 3.67/1.61  
% 3.67/1.61  #Partial instantiations: 0
% 3.67/1.61  #Strategies tried      : 1
% 3.67/1.61  
% 3.67/1.61  Timing (in seconds)
% 3.67/1.61  ----------------------
% 3.67/1.61  Preprocessing        : 0.30
% 3.67/1.61  Parsing              : 0.15
% 3.67/1.61  CNF conversion       : 0.02
% 3.67/1.61  Main loop            : 0.57
% 3.67/1.61  Inferencing          : 0.20
% 3.67/1.61  Reduction            : 0.17
% 3.67/1.61  Demodulation         : 0.09
% 3.67/1.62  BG Simplification    : 0.02
% 3.67/1.62  Subsumption          : 0.13
% 3.67/1.62  Abstraction          : 0.03
% 3.67/1.62  MUC search           : 0.00
% 3.67/1.62  Cooper               : 0.00
% 3.67/1.62  Total                : 0.89
% 3.67/1.62  Index Insertion      : 0.00
% 3.67/1.62  Index Deletion       : 0.00
% 3.67/1.62  Index Matching       : 0.00
% 3.67/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
