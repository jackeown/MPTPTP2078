%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:22 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   58 (  87 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 ( 125 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_780,plain,(
    ! [A_141,C_142,B_143] :
      ( ~ r2_hidden(A_141,C_142)
      | ~ r1_xboole_0(k2_tarski(A_141,B_143),C_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_785,plain,(
    ! [A_141] : ~ r2_hidden(A_141,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_780])).

tff(c_36,plain,
    ( k11_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_53,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_42,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | k11_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_54,plain,(
    k11_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_42])).

tff(c_34,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_406,plain,(
    ! [A_130,B_131] :
      ( r2_hidden(k4_tarski('#skF_1'(A_130,B_131),'#skF_2'(A_130,B_131)),A_130)
      | r2_hidden('#skF_3'(A_130,B_131),B_131)
      | k1_relat_1(A_130) = B_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_55,plain,(
    ! [A_57,C_58,B_59] :
      ( ~ r2_hidden(A_57,C_58)
      | ~ r1_xboole_0(k2_tarski(A_57,B_59),C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_60,plain,(
    ! [A_57] : ~ r2_hidden(A_57,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_55])).

tff(c_499,plain,(
    ! [B_132] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_132),B_132)
      | k1_relat_1(k1_xboole_0) = B_132 ) ),
    inference(resolution,[status(thm)],[c_406,c_60])).

tff(c_584,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_499,c_60])).

tff(c_498,plain,(
    ! [B_131] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_131),B_131)
      | k1_relat_1(k1_xboole_0) = B_131 ) ),
    inference(resolution,[status(thm)],[c_406,c_60])).

tff(c_625,plain,(
    ! [B_136] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_136),B_136)
      | k1_xboole_0 = B_136 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_498])).

tff(c_82,plain,(
    ! [A_74,B_75,C_76] :
      ( r2_hidden(k4_tarski(A_74,B_75),C_76)
      | ~ r2_hidden(B_75,k11_relat_1(C_76,A_74))
      | ~ v1_relat_1(C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    ! [C_47,A_32,D_50] :
      ( r2_hidden(C_47,k1_relat_1(A_32))
      | ~ r2_hidden(k4_tarski(C_47,D_50),A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_94,plain,(
    ! [A_74,C_76,B_75] :
      ( r2_hidden(A_74,k1_relat_1(C_76))
      | ~ r2_hidden(B_75,k11_relat_1(C_76,A_74))
      | ~ v1_relat_1(C_76) ) ),
    inference(resolution,[status(thm)],[c_82,c_20])).

tff(c_713,plain,(
    ! [A_139,C_140] :
      ( r2_hidden(A_139,k1_relat_1(C_140))
      | ~ v1_relat_1(C_140)
      | k11_relat_1(C_140,A_139) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_625,c_94])).

tff(c_746,plain,
    ( ~ v1_relat_1('#skF_6')
    | k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_713,c_53])).

tff(c_760,plain,(
    k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_746])).

tff(c_762,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_760])).

tff(c_764,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_763,plain,(
    k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_850,plain,(
    ! [C_171,A_172] :
      ( r2_hidden(k4_tarski(C_171,'#skF_4'(A_172,k1_relat_1(A_172),C_171)),A_172)
      | ~ r2_hidden(C_171,k1_relat_1(A_172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    ! [B_52,C_53,A_51] :
      ( r2_hidden(B_52,k11_relat_1(C_53,A_51))
      | ~ r2_hidden(k4_tarski(A_51,B_52),C_53)
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1536,plain,(
    ! [A_225,C_226] :
      ( r2_hidden('#skF_4'(A_225,k1_relat_1(A_225),C_226),k11_relat_1(A_225,C_226))
      | ~ v1_relat_1(A_225)
      | ~ r2_hidden(C_226,k1_relat_1(A_225)) ) ),
    inference(resolution,[status(thm)],[c_850,c_32])).

tff(c_1550,plain,
    ( r2_hidden('#skF_4'('#skF_6',k1_relat_1('#skF_6'),'#skF_5'),k1_xboole_0)
    | ~ v1_relat_1('#skF_6')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_1536])).

tff(c_1555,plain,(
    r2_hidden('#skF_4'('#skF_6',k1_relat_1('#skF_6'),'#skF_5'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_34,c_1550])).

tff(c_1557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_785,c_1555])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.50  
% 3.04/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.51  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 3.04/1.51  
% 3.04/1.51  %Foreground sorts:
% 3.04/1.51  
% 3.04/1.51  
% 3.04/1.51  %Background operators:
% 3.04/1.51  
% 3.04/1.51  
% 3.04/1.51  %Foreground operators:
% 3.04/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.04/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.04/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.04/1.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.04/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.04/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.04/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.04/1.51  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.04/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.04/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.04/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.04/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.04/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.04/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.04/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.04/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.04/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.04/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.04/1.51  
% 3.43/1.52  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.43/1.52  tff(f_44, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.43/1.52  tff(f_66, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.43/1.52  tff(f_52, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.43/1.52  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 3.43/1.52  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.43/1.52  tff(c_780, plain, (![A_141, C_142, B_143]: (~r2_hidden(A_141, C_142) | ~r1_xboole_0(k2_tarski(A_141, B_143), C_142))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.43/1.52  tff(c_785, plain, (![A_141]: (~r2_hidden(A_141, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_780])).
% 3.43/1.52  tff(c_36, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | ~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.43/1.52  tff(c_53, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_36])).
% 3.43/1.52  tff(c_42, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6')) | k11_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.43/1.52  tff(c_54, plain, (k11_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_53, c_42])).
% 3.43/1.52  tff(c_34, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.43/1.52  tff(c_406, plain, (![A_130, B_131]: (r2_hidden(k4_tarski('#skF_1'(A_130, B_131), '#skF_2'(A_130, B_131)), A_130) | r2_hidden('#skF_3'(A_130, B_131), B_131) | k1_relat_1(A_130)=B_131)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.43/1.52  tff(c_55, plain, (![A_57, C_58, B_59]: (~r2_hidden(A_57, C_58) | ~r1_xboole_0(k2_tarski(A_57, B_59), C_58))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.43/1.52  tff(c_60, plain, (![A_57]: (~r2_hidden(A_57, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_55])).
% 3.43/1.52  tff(c_499, plain, (![B_132]: (r2_hidden('#skF_3'(k1_xboole_0, B_132), B_132) | k1_relat_1(k1_xboole_0)=B_132)), inference(resolution, [status(thm)], [c_406, c_60])).
% 3.43/1.52  tff(c_584, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_499, c_60])).
% 3.43/1.52  tff(c_498, plain, (![B_131]: (r2_hidden('#skF_3'(k1_xboole_0, B_131), B_131) | k1_relat_1(k1_xboole_0)=B_131)), inference(resolution, [status(thm)], [c_406, c_60])).
% 3.43/1.52  tff(c_625, plain, (![B_136]: (r2_hidden('#skF_3'(k1_xboole_0, B_136), B_136) | k1_xboole_0=B_136)), inference(demodulation, [status(thm), theory('equality')], [c_584, c_498])).
% 3.43/1.52  tff(c_82, plain, (![A_74, B_75, C_76]: (r2_hidden(k4_tarski(A_74, B_75), C_76) | ~r2_hidden(B_75, k11_relat_1(C_76, A_74)) | ~v1_relat_1(C_76))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.43/1.52  tff(c_20, plain, (![C_47, A_32, D_50]: (r2_hidden(C_47, k1_relat_1(A_32)) | ~r2_hidden(k4_tarski(C_47, D_50), A_32))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.43/1.52  tff(c_94, plain, (![A_74, C_76, B_75]: (r2_hidden(A_74, k1_relat_1(C_76)) | ~r2_hidden(B_75, k11_relat_1(C_76, A_74)) | ~v1_relat_1(C_76))), inference(resolution, [status(thm)], [c_82, c_20])).
% 3.43/1.52  tff(c_713, plain, (![A_139, C_140]: (r2_hidden(A_139, k1_relat_1(C_140)) | ~v1_relat_1(C_140) | k11_relat_1(C_140, A_139)=k1_xboole_0)), inference(resolution, [status(thm)], [c_625, c_94])).
% 3.43/1.52  tff(c_746, plain, (~v1_relat_1('#skF_6') | k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_713, c_53])).
% 3.43/1.52  tff(c_760, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_746])).
% 3.43/1.52  tff(c_762, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_760])).
% 3.43/1.52  tff(c_764, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_36])).
% 3.43/1.52  tff(c_763, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 3.43/1.52  tff(c_850, plain, (![C_171, A_172]: (r2_hidden(k4_tarski(C_171, '#skF_4'(A_172, k1_relat_1(A_172), C_171)), A_172) | ~r2_hidden(C_171, k1_relat_1(A_172)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.43/1.52  tff(c_32, plain, (![B_52, C_53, A_51]: (r2_hidden(B_52, k11_relat_1(C_53, A_51)) | ~r2_hidden(k4_tarski(A_51, B_52), C_53) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.43/1.52  tff(c_1536, plain, (![A_225, C_226]: (r2_hidden('#skF_4'(A_225, k1_relat_1(A_225), C_226), k11_relat_1(A_225, C_226)) | ~v1_relat_1(A_225) | ~r2_hidden(C_226, k1_relat_1(A_225)))), inference(resolution, [status(thm)], [c_850, c_32])).
% 3.43/1.52  tff(c_1550, plain, (r2_hidden('#skF_4'('#skF_6', k1_relat_1('#skF_6'), '#skF_5'), k1_xboole_0) | ~v1_relat_1('#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_763, c_1536])).
% 3.43/1.52  tff(c_1555, plain, (r2_hidden('#skF_4'('#skF_6', k1_relat_1('#skF_6'), '#skF_5'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_764, c_34, c_1550])).
% 3.43/1.52  tff(c_1557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_785, c_1555])).
% 3.43/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.52  
% 3.43/1.52  Inference rules
% 3.43/1.52  ----------------------
% 3.43/1.52  #Ref     : 0
% 3.43/1.52  #Sup     : 295
% 3.43/1.52  #Fact    : 0
% 3.43/1.52  #Define  : 0
% 3.43/1.52  #Split   : 11
% 3.43/1.52  #Chain   : 0
% 3.43/1.52  #Close   : 0
% 3.43/1.52  
% 3.43/1.52  Ordering : KBO
% 3.43/1.52  
% 3.43/1.52  Simplification rules
% 3.43/1.52  ----------------------
% 3.43/1.52  #Subsume      : 87
% 3.43/1.52  #Demod        : 242
% 3.43/1.52  #Tautology    : 63
% 3.43/1.52  #SimpNegUnit  : 16
% 3.43/1.52  #BackRed      : 29
% 3.43/1.52  
% 3.43/1.52  #Partial instantiations: 0
% 3.43/1.52  #Strategies tried      : 1
% 3.43/1.52  
% 3.43/1.52  Timing (in seconds)
% 3.43/1.52  ----------------------
% 3.43/1.52  Preprocessing        : 0.32
% 3.43/1.52  Parsing              : 0.16
% 3.43/1.52  CNF conversion       : 0.02
% 3.43/1.52  Main loop            : 0.44
% 3.43/1.52  Inferencing          : 0.17
% 3.43/1.52  Reduction            : 0.12
% 3.43/1.52  Demodulation         : 0.08
% 3.43/1.52  BG Simplification    : 0.03
% 3.43/1.52  Subsumption          : 0.09
% 3.43/1.52  Abstraction          : 0.03
% 3.43/1.52  MUC search           : 0.00
% 3.43/1.52  Cooper               : 0.00
% 3.43/1.52  Total                : 0.79
% 3.43/1.52  Index Insertion      : 0.00
% 3.43/1.52  Index Deletion       : 0.00
% 3.43/1.52  Index Matching       : 0.00
% 3.43/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
