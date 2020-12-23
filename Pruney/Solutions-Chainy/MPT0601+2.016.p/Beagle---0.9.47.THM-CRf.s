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
% DateTime   : Thu Dec  3 10:02:16 EST 2020

% Result     : Theorem 7.70s
% Output     : CNFRefutation 7.70s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 125 expanded)
%              Number of leaves         :   35 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  111 ( 196 expanded)
%              Number of equality atoms :   28 (  61 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_3 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_95,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_7604,plain,(
    ! [A_334,B_335] :
      ( k2_xboole_0(k1_tarski(A_334),B_335) = B_335
      | ~ r2_hidden(A_334,B_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    ! [A_12,B_13] : k2_xboole_0(k1_tarski(A_12),B_13) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7615,plain,(
    ! [A_334] : ~ r2_hidden(A_334,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7604,c_28])).

tff(c_20,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89,plain,(
    ! [A_53,B_54] :
      ( v1_relat_1(k3_xboole_0(A_53,B_54))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_92,plain,(
    ! [A_7] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_89])).

tff(c_93,plain,(
    ! [A_7] : ~ v1_relat_1(A_7) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_64,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_96,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_64])).

tff(c_97,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_60,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_62,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_7718,plain,(
    ! [A_363,B_364] :
      ( r2_hidden('#skF_8'(A_363,B_364),k1_relat_1(B_364))
      | ~ r2_hidden(A_363,k2_relat_1(B_364))
      | ~ v1_relat_1(B_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_7726,plain,(
    ! [A_363] :
      ( r2_hidden('#skF_8'(A_363,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_363,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_7718])).

tff(c_7730,plain,(
    ! [A_363] :
      ( r2_hidden('#skF_8'(A_363,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_363,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_60,c_7726])).

tff(c_7731,plain,(
    ! [A_363] : ~ r2_hidden(A_363,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_7615,c_7730])).

tff(c_66,plain,
    ( k11_relat_1('#skF_10','#skF_9') = k1_xboole_0
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_98,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,
    ( r2_hidden('#skF_9',k1_relat_1('#skF_10'))
    | k11_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_113,plain,(
    k11_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_72])).

tff(c_1251,plain,(
    ! [A_181,B_182,C_183] :
      ( r2_hidden('#skF_1'(A_181,B_182,C_183),A_181)
      | r2_hidden('#skF_2'(A_181,B_182,C_183),C_183)
      | k4_xboole_0(A_181,B_182) = C_183 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1596,plain,(
    ! [A_184,B_185] :
      ( r2_hidden('#skF_2'(A_184,B_185,A_184),A_184)
      | k4_xboole_0(A_184,B_185) = A_184 ) ),
    inference(resolution,[status(thm)],[c_1251,c_14])).

tff(c_99,plain,(
    ! [A_55,B_56] :
      ( k2_xboole_0(k1_tarski(A_55),B_56) = B_56
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_104,plain,(
    ! [B_56,A_55] :
      ( k1_xboole_0 != B_56
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_28])).

tff(c_1789,plain,(
    ! [B_185] : k4_xboole_0(k1_xboole_0,B_185) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1596,c_104])).

tff(c_110,plain,(
    ! [A_55] : ~ r2_hidden(A_55,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_28])).

tff(c_173,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_8'(A_83,B_84),k1_relat_1(B_84))
      | ~ r2_hidden(A_83,k2_relat_1(B_84))
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_181,plain,(
    ! [A_83] :
      ( r2_hidden('#skF_8'(A_83,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_83,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_173])).

tff(c_185,plain,(
    ! [A_83] :
      ( r2_hidden('#skF_8'(A_83,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_83,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_60,c_181])).

tff(c_186,plain,(
    ! [A_83] : ~ r2_hidden(A_83,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_185])).

tff(c_1557,plain,(
    ! [B_182,C_183] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_182,C_183),C_183)
      | k4_xboole_0(k1_xboole_0,B_182) = C_183 ) ),
    inference(resolution,[status(thm)],[c_1251,c_186])).

tff(c_5478,plain,(
    ! [B_281,C_282] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_281,C_282),C_282)
      | k1_xboole_0 = C_282 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1789,c_1557])).

tff(c_200,plain,(
    ! [A_91,B_92,C_93] :
      ( r2_hidden(k4_tarski(A_91,B_92),C_93)
      | ~ r2_hidden(B_92,k11_relat_1(C_93,A_91))
      | ~ v1_relat_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    ! [C_32,A_17,D_35] :
      ( r2_hidden(C_32,k1_relat_1(A_17))
      | ~ r2_hidden(k4_tarski(C_32,D_35),A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_234,plain,(
    ! [A_91,C_93,B_92] :
      ( r2_hidden(A_91,k1_relat_1(C_93))
      | ~ r2_hidden(B_92,k11_relat_1(C_93,A_91))
      | ~ v1_relat_1(C_93) ) ),
    inference(resolution,[status(thm)],[c_200,c_34])).

tff(c_7440,plain,(
    ! [A_326,C_327] :
      ( r2_hidden(A_326,k1_relat_1(C_327))
      | ~ v1_relat_1(C_327)
      | k11_relat_1(C_327,A_326) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_5478,c_234])).

tff(c_7525,plain,
    ( ~ v1_relat_1('#skF_10')
    | k11_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7440,c_98])).

tff(c_7591,plain,(
    k11_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_7525])).

tff(c_7593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_7591])).

tff(c_7595,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_7594,plain,(
    k11_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_7899,plain,(
    ! [C_398,A_399] :
      ( r2_hidden(k4_tarski(C_398,'#skF_6'(A_399,k1_relat_1(A_399),C_398)),A_399)
      | ~ r2_hidden(C_398,k1_relat_1(A_399)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_58,plain,(
    ! [B_48,C_49,A_47] :
      ( r2_hidden(B_48,k11_relat_1(C_49,A_47))
      | ~ r2_hidden(k4_tarski(A_47,B_48),C_49)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_12248,plain,(
    ! [A_547,C_548] :
      ( r2_hidden('#skF_6'(A_547,k1_relat_1(A_547),C_548),k11_relat_1(A_547,C_548))
      | ~ v1_relat_1(A_547)
      | ~ r2_hidden(C_548,k1_relat_1(A_547)) ) ),
    inference(resolution,[status(thm)],[c_7899,c_58])).

tff(c_12302,plain,
    ( r2_hidden('#skF_6'('#skF_10',k1_relat_1('#skF_10'),'#skF_9'),k1_xboole_0)
    | ~ v1_relat_1('#skF_10')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7594,c_12248])).

tff(c_12317,plain,(
    r2_hidden('#skF_6'('#skF_10',k1_relat_1('#skF_10'),'#skF_9'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7595,c_64,c_12302])).

tff(c_12319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7731,c_12317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:50:25 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.70/2.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.70/2.69  
% 7.70/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.70/2.70  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_3 > #skF_10 > #skF_2 > #skF_8 > #skF_9 > #skF_7 > #skF_5 > #skF_4
% 7.70/2.70  
% 7.70/2.70  %Foreground sorts:
% 7.70/2.70  
% 7.70/2.70  
% 7.70/2.70  %Background operators:
% 7.70/2.70  
% 7.70/2.70  
% 7.70/2.70  %Foreground operators:
% 7.70/2.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.70/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.70/2.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.70/2.70  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.70/2.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.70/2.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.70/2.70  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.70/2.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.70/2.70  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.70/2.70  tff('#skF_10', type, '#skF_10': $i).
% 7.70/2.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.70/2.70  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 7.70/2.70  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.70/2.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.70/2.70  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 7.70/2.70  tff('#skF_9', type, '#skF_9': $i).
% 7.70/2.70  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 7.70/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.70/2.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.70/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.70/2.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.70/2.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.70/2.70  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.70/2.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.70/2.70  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.70/2.70  
% 7.70/2.71  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 7.70/2.71  tff(f_49, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 7.70/2.71  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 7.70/2.71  tff(f_66, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 7.70/2.71  tff(f_103, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 7.70/2.71  tff(f_95, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 7.70/2.71  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 7.70/2.71  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.70/2.71  tff(f_92, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 7.70/2.71  tff(f_62, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 7.70/2.71  tff(c_7604, plain, (![A_334, B_335]: (k2_xboole_0(k1_tarski(A_334), B_335)=B_335 | ~r2_hidden(A_334, B_335))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.70/2.71  tff(c_28, plain, (![A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.70/2.71  tff(c_7615, plain, (![A_334]: (~r2_hidden(A_334, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7604, c_28])).
% 7.70/2.71  tff(c_20, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.70/2.71  tff(c_89, plain, (![A_53, B_54]: (v1_relat_1(k3_xboole_0(A_53, B_54)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.70/2.71  tff(c_92, plain, (![A_7]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_89])).
% 7.70/2.71  tff(c_93, plain, (![A_7]: (~v1_relat_1(A_7))), inference(splitLeft, [status(thm)], [c_92])).
% 7.70/2.71  tff(c_64, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.70/2.71  tff(c_96, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_64])).
% 7.70/2.71  tff(c_97, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_92])).
% 7.70/2.71  tff(c_60, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.70/2.71  tff(c_62, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.70/2.71  tff(c_7718, plain, (![A_363, B_364]: (r2_hidden('#skF_8'(A_363, B_364), k1_relat_1(B_364)) | ~r2_hidden(A_363, k2_relat_1(B_364)) | ~v1_relat_1(B_364))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.70/2.71  tff(c_7726, plain, (![A_363]: (r2_hidden('#skF_8'(A_363, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_363, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_62, c_7718])).
% 7.70/2.71  tff(c_7730, plain, (![A_363]: (r2_hidden('#skF_8'(A_363, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_363, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_60, c_7726])).
% 7.70/2.71  tff(c_7731, plain, (![A_363]: (~r2_hidden(A_363, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_7615, c_7730])).
% 7.70/2.71  tff(c_66, plain, (k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0 | ~r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.70/2.71  tff(c_98, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_66])).
% 7.70/2.71  tff(c_72, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10')) | k11_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.70/2.71  tff(c_113, plain, (k11_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_98, c_72])).
% 7.70/2.71  tff(c_1251, plain, (![A_181, B_182, C_183]: (r2_hidden('#skF_1'(A_181, B_182, C_183), A_181) | r2_hidden('#skF_2'(A_181, B_182, C_183), C_183) | k4_xboole_0(A_181, B_182)=C_183)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.70/2.71  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.70/2.71  tff(c_1596, plain, (![A_184, B_185]: (r2_hidden('#skF_2'(A_184, B_185, A_184), A_184) | k4_xboole_0(A_184, B_185)=A_184)), inference(resolution, [status(thm)], [c_1251, c_14])).
% 7.70/2.71  tff(c_99, plain, (![A_55, B_56]: (k2_xboole_0(k1_tarski(A_55), B_56)=B_56 | ~r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.70/2.71  tff(c_104, plain, (![B_56, A_55]: (k1_xboole_0!=B_56 | ~r2_hidden(A_55, B_56))), inference(superposition, [status(thm), theory('equality')], [c_99, c_28])).
% 7.70/2.71  tff(c_1789, plain, (![B_185]: (k4_xboole_0(k1_xboole_0, B_185)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1596, c_104])).
% 7.70/2.71  tff(c_110, plain, (![A_55]: (~r2_hidden(A_55, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_99, c_28])).
% 7.70/2.71  tff(c_173, plain, (![A_83, B_84]: (r2_hidden('#skF_8'(A_83, B_84), k1_relat_1(B_84)) | ~r2_hidden(A_83, k2_relat_1(B_84)) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.70/2.71  tff(c_181, plain, (![A_83]: (r2_hidden('#skF_8'(A_83, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_83, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_62, c_173])).
% 7.70/2.71  tff(c_185, plain, (![A_83]: (r2_hidden('#skF_8'(A_83, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_83, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_60, c_181])).
% 7.70/2.71  tff(c_186, plain, (![A_83]: (~r2_hidden(A_83, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_110, c_185])).
% 7.70/2.71  tff(c_1557, plain, (![B_182, C_183]: (r2_hidden('#skF_2'(k1_xboole_0, B_182, C_183), C_183) | k4_xboole_0(k1_xboole_0, B_182)=C_183)), inference(resolution, [status(thm)], [c_1251, c_186])).
% 7.70/2.71  tff(c_5478, plain, (![B_281, C_282]: (r2_hidden('#skF_2'(k1_xboole_0, B_281, C_282), C_282) | k1_xboole_0=C_282)), inference(demodulation, [status(thm), theory('equality')], [c_1789, c_1557])).
% 7.70/2.71  tff(c_200, plain, (![A_91, B_92, C_93]: (r2_hidden(k4_tarski(A_91, B_92), C_93) | ~r2_hidden(B_92, k11_relat_1(C_93, A_91)) | ~v1_relat_1(C_93))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.70/2.71  tff(c_34, plain, (![C_32, A_17, D_35]: (r2_hidden(C_32, k1_relat_1(A_17)) | ~r2_hidden(k4_tarski(C_32, D_35), A_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.70/2.71  tff(c_234, plain, (![A_91, C_93, B_92]: (r2_hidden(A_91, k1_relat_1(C_93)) | ~r2_hidden(B_92, k11_relat_1(C_93, A_91)) | ~v1_relat_1(C_93))), inference(resolution, [status(thm)], [c_200, c_34])).
% 7.70/2.71  tff(c_7440, plain, (![A_326, C_327]: (r2_hidden(A_326, k1_relat_1(C_327)) | ~v1_relat_1(C_327) | k11_relat_1(C_327, A_326)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5478, c_234])).
% 7.70/2.71  tff(c_7525, plain, (~v1_relat_1('#skF_10') | k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_7440, c_98])).
% 7.70/2.71  tff(c_7591, plain, (k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_7525])).
% 7.70/2.71  tff(c_7593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_7591])).
% 7.70/2.71  tff(c_7595, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_66])).
% 7.70/2.71  tff(c_7594, plain, (k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 7.70/2.71  tff(c_7899, plain, (![C_398, A_399]: (r2_hidden(k4_tarski(C_398, '#skF_6'(A_399, k1_relat_1(A_399), C_398)), A_399) | ~r2_hidden(C_398, k1_relat_1(A_399)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.70/2.71  tff(c_58, plain, (![B_48, C_49, A_47]: (r2_hidden(B_48, k11_relat_1(C_49, A_47)) | ~r2_hidden(k4_tarski(A_47, B_48), C_49) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.70/2.71  tff(c_12248, plain, (![A_547, C_548]: (r2_hidden('#skF_6'(A_547, k1_relat_1(A_547), C_548), k11_relat_1(A_547, C_548)) | ~v1_relat_1(A_547) | ~r2_hidden(C_548, k1_relat_1(A_547)))), inference(resolution, [status(thm)], [c_7899, c_58])).
% 7.70/2.71  tff(c_12302, plain, (r2_hidden('#skF_6'('#skF_10', k1_relat_1('#skF_10'), '#skF_9'), k1_xboole_0) | ~v1_relat_1('#skF_10') | ~r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_7594, c_12248])).
% 7.70/2.71  tff(c_12317, plain, (r2_hidden('#skF_6'('#skF_10', k1_relat_1('#skF_10'), '#skF_9'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7595, c_64, c_12302])).
% 7.70/2.71  tff(c_12319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7731, c_12317])).
% 7.70/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.70/2.71  
% 7.70/2.71  Inference rules
% 7.70/2.71  ----------------------
% 7.70/2.71  #Ref     : 2
% 7.70/2.71  #Sup     : 2795
% 7.70/2.71  #Fact    : 0
% 7.70/2.71  #Define  : 0
% 7.70/2.71  #Split   : 5
% 7.70/2.71  #Chain   : 0
% 7.70/2.71  #Close   : 0
% 7.70/2.71  
% 7.70/2.71  Ordering : KBO
% 7.70/2.71  
% 7.70/2.71  Simplification rules
% 7.70/2.71  ----------------------
% 7.70/2.71  #Subsume      : 961
% 7.70/2.71  #Demod        : 752
% 7.70/2.71  #Tautology    : 540
% 7.70/2.71  #SimpNegUnit  : 84
% 7.70/2.71  #BackRed      : 34
% 7.70/2.71  
% 7.70/2.71  #Partial instantiations: 0
% 7.70/2.71  #Strategies tried      : 1
% 7.70/2.71  
% 7.70/2.71  Timing (in seconds)
% 7.70/2.71  ----------------------
% 7.70/2.71  Preprocessing        : 0.32
% 7.70/2.71  Parsing              : 0.18
% 7.70/2.71  CNF conversion       : 0.03
% 7.70/2.71  Main loop            : 1.63
% 7.70/2.72  Inferencing          : 0.51
% 7.70/2.72  Reduction            : 0.43
% 7.70/2.72  Demodulation         : 0.28
% 7.70/2.72  BG Simplification    : 0.06
% 7.70/2.72  Subsumption          : 0.49
% 7.70/2.72  Abstraction          : 0.09
% 7.70/2.72  MUC search           : 0.00
% 7.70/2.72  Cooper               : 0.00
% 7.70/2.72  Total                : 1.98
% 7.70/2.72  Index Insertion      : 0.00
% 7.70/2.72  Index Deletion       : 0.00
% 7.70/2.72  Index Matching       : 0.00
% 7.70/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
