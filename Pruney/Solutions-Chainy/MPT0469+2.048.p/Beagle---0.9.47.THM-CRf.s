%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:57 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   57 (  91 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 ( 110 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_8 > #skF_7 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(c_38,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_398,plain,(
    ! [A_135,B_136] :
      ( r2_hidden(k4_tarski('#skF_5'(A_135,B_136),'#skF_4'(A_135,B_136)),A_135)
      | r2_hidden('#skF_6'(A_135,B_136),B_136)
      | k2_relat_1(A_135) = B_136 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    ! [A_79,C_80,B_81] :
      ( ~ r2_hidden(A_79,C_80)
      | ~ r1_xboole_0(k2_tarski(A_79,B_81),C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_57,plain,(
    ! [A_79] : ~ r2_hidden(A_79,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_1123,plain,(
    ! [B_162] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_162),B_162)
      | k2_relat_1(k1_xboole_0) = B_162 ) ),
    inference(resolution,[status(thm)],[c_398,c_57])).

tff(c_1264,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1123,c_57])).

tff(c_22,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_1'(A_32),A_32)
      | v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58,plain,(
    ! [A_82] : ~ r2_hidden(A_82,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_63,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_58])).

tff(c_36,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_8'(A_69,B_70),k2_relat_1(B_70))
      | ~ r2_hidden(A_69,k1_relat_1(B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_84,plain,(
    ! [A_95,C_96] :
      ( r2_hidden(k4_tarski('#skF_7'(A_95,k2_relat_1(A_95),C_96),C_96),A_95)
      | ~ r2_hidden(C_96,k2_relat_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_94,plain,(
    ! [C_97] : ~ r2_hidden(C_97,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_84,c_57])).

tff(c_102,plain,(
    ! [A_69] :
      ( ~ r2_hidden(A_69,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_94])).

tff(c_110,plain,(
    ! [A_69] : ~ r2_hidden(A_69,k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_102])).

tff(c_1261,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1123,c_110])).

tff(c_1335,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1264,c_1261])).

tff(c_1336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1335])).

tff(c_1337,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1684,plain,(
    ! [A_224,B_225] :
      ( r2_hidden(k4_tarski('#skF_5'(A_224,B_225),'#skF_4'(A_224,B_225)),A_224)
      | r2_hidden('#skF_6'(A_224,B_225),B_225)
      | k2_relat_1(A_224) = B_225 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1354,plain,(
    ! [A_169,C_170,B_171] :
      ( ~ r2_hidden(A_169,C_170)
      | ~ r1_xboole_0(k2_tarski(A_169,B_171),C_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1359,plain,(
    ! [A_169] : ~ r2_hidden(A_169,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_1354])).

tff(c_1829,plain,(
    ! [B_232] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_232),B_232)
      | k2_relat_1(k1_xboole_0) = B_232 ) ),
    inference(resolution,[status(thm)],[c_1684,c_1359])).

tff(c_1893,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1829,c_1359])).

tff(c_1913,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1337,c_1893])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.63  
% 3.67/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.63  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_8 > #skF_7 > #skF_2 > #skF_5 > #skF_4
% 3.67/1.63  
% 3.67/1.63  %Foreground sorts:
% 3.67/1.63  
% 3.67/1.63  
% 3.67/1.63  %Background operators:
% 3.67/1.63  
% 3.67/1.63  
% 3.67/1.63  %Foreground operators:
% 3.67/1.63  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.67/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.67/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.67/1.63  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.67/1.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.67/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.67/1.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.67/1.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.67/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.67/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.67/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.67/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.67/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.67/1.63  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.67/1.63  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.67/1.63  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.67/1.63  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.67/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.67/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.67/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.67/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.67/1.63  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.67/1.63  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.67/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.67/1.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.67/1.63  
% 3.67/1.64  tff(f_75, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.67/1.64  tff(f_62, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 3.67/1.64  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.67/1.64  tff(f_44, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.67/1.64  tff(f_54, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 3.67/1.64  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 3.67/1.64  tff(c_38, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.67/1.64  tff(c_40, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 3.67/1.64  tff(c_398, plain, (![A_135, B_136]: (r2_hidden(k4_tarski('#skF_5'(A_135, B_136), '#skF_4'(A_135, B_136)), A_135) | r2_hidden('#skF_6'(A_135, B_136), B_136) | k2_relat_1(A_135)=B_136)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.67/1.64  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.67/1.64  tff(c_52, plain, (![A_79, C_80, B_81]: (~r2_hidden(A_79, C_80) | ~r1_xboole_0(k2_tarski(A_79, B_81), C_80))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.67/1.64  tff(c_57, plain, (![A_79]: (~r2_hidden(A_79, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_52])).
% 3.67/1.64  tff(c_1123, plain, (![B_162]: (r2_hidden('#skF_6'(k1_xboole_0, B_162), B_162) | k2_relat_1(k1_xboole_0)=B_162)), inference(resolution, [status(thm)], [c_398, c_57])).
% 3.67/1.64  tff(c_1264, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1123, c_57])).
% 3.67/1.64  tff(c_22, plain, (![A_32]: (r2_hidden('#skF_1'(A_32), A_32) | v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.67/1.64  tff(c_58, plain, (![A_82]: (~r2_hidden(A_82, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_52])).
% 3.67/1.64  tff(c_63, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_58])).
% 3.67/1.64  tff(c_36, plain, (![A_69, B_70]: (r2_hidden('#skF_8'(A_69, B_70), k2_relat_1(B_70)) | ~r2_hidden(A_69, k1_relat_1(B_70)) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.67/1.64  tff(c_84, plain, (![A_95, C_96]: (r2_hidden(k4_tarski('#skF_7'(A_95, k2_relat_1(A_95), C_96), C_96), A_95) | ~r2_hidden(C_96, k2_relat_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.67/1.64  tff(c_94, plain, (![C_97]: (~r2_hidden(C_97, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_84, c_57])).
% 3.67/1.64  tff(c_102, plain, (![A_69]: (~r2_hidden(A_69, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_94])).
% 3.67/1.64  tff(c_110, plain, (![A_69]: (~r2_hidden(A_69, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_102])).
% 3.67/1.64  tff(c_1261, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_1123, c_110])).
% 3.67/1.64  tff(c_1335, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1264, c_1261])).
% 3.67/1.64  tff(c_1336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1335])).
% 3.67/1.64  tff(c_1337, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 3.67/1.64  tff(c_1684, plain, (![A_224, B_225]: (r2_hidden(k4_tarski('#skF_5'(A_224, B_225), '#skF_4'(A_224, B_225)), A_224) | r2_hidden('#skF_6'(A_224, B_225), B_225) | k2_relat_1(A_224)=B_225)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.67/1.64  tff(c_1354, plain, (![A_169, C_170, B_171]: (~r2_hidden(A_169, C_170) | ~r1_xboole_0(k2_tarski(A_169, B_171), C_170))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.67/1.64  tff(c_1359, plain, (![A_169]: (~r2_hidden(A_169, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_1354])).
% 3.67/1.64  tff(c_1829, plain, (![B_232]: (r2_hidden('#skF_6'(k1_xboole_0, B_232), B_232) | k2_relat_1(k1_xboole_0)=B_232)), inference(resolution, [status(thm)], [c_1684, c_1359])).
% 3.67/1.64  tff(c_1893, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1829, c_1359])).
% 3.67/1.64  tff(c_1913, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1337, c_1893])).
% 3.67/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.64  
% 3.67/1.64  Inference rules
% 3.67/1.64  ----------------------
% 3.67/1.64  #Ref     : 1
% 3.67/1.64  #Sup     : 348
% 3.67/1.64  #Fact    : 0
% 3.67/1.64  #Define  : 0
% 3.67/1.64  #Split   : 1
% 3.67/1.64  #Chain   : 0
% 3.67/1.64  #Close   : 0
% 3.67/1.64  
% 3.67/1.64  Ordering : KBO
% 3.67/1.64  
% 3.67/1.64  Simplification rules
% 3.67/1.64  ----------------------
% 3.67/1.64  #Subsume      : 78
% 3.67/1.64  #Demod        : 96
% 3.67/1.64  #Tautology    : 51
% 3.67/1.64  #SimpNegUnit  : 6
% 3.67/1.64  #BackRed      : 31
% 3.67/1.64  
% 3.67/1.64  #Partial instantiations: 0
% 3.67/1.64  #Strategies tried      : 1
% 3.67/1.64  
% 3.67/1.64  Timing (in seconds)
% 3.67/1.64  ----------------------
% 3.67/1.64  Preprocessing        : 0.34
% 3.67/1.64  Parsing              : 0.18
% 3.67/1.64  CNF conversion       : 0.02
% 3.67/1.64  Main loop            : 0.51
% 3.67/1.64  Inferencing          : 0.18
% 3.67/1.64  Reduction            : 0.15
% 3.67/1.64  Demodulation         : 0.09
% 3.67/1.64  BG Simplification    : 0.02
% 3.67/1.64  Subsumption          : 0.11
% 3.67/1.64  Abstraction          : 0.03
% 3.67/1.64  MUC search           : 0.00
% 3.67/1.64  Cooper               : 0.00
% 3.67/1.64  Total                : 0.87
% 3.67/1.64  Index Insertion      : 0.00
% 3.67/1.64  Index Deletion       : 0.00
% 3.67/1.64  Index Matching       : 0.00
% 3.67/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
