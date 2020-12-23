%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:55 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   55 (  85 expanded)
%              Number of leaves         :   29 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 ( 104 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1 > #skF_5

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_68,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(c_34,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_50,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_359,plain,(
    ! [A_86,B_87] :
      ( r2_hidden(k4_tarski('#skF_2'(A_86,B_87),'#skF_1'(A_86,B_87)),A_86)
      | r2_hidden('#skF_3'(A_86,B_87),B_87)
      | k2_relat_1(A_86) = B_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_60,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden(A_47,B_48)
      | ~ r1_xboole_0(k1_tarski(A_47),B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_65,plain,(
    ! [A_47] : ~ r2_hidden(A_47,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_60])).

tff(c_456,plain,(
    ! [B_90] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_90),B_90)
      | k2_relat_1(k1_xboole_0) = B_90 ) ),
    inference(resolution,[status(thm)],[c_359,c_65])).

tff(c_517,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_456,c_65])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    ! [A_43] :
      ( v1_relat_1(A_43)
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_36])).

tff(c_32,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_5'(A_39,B_40),k2_relat_1(B_40))
      | ~ r2_hidden(A_39,k1_relat_1(B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_87,plain,(
    ! [A_62,C_63] :
      ( r2_hidden(k4_tarski('#skF_4'(A_62,k2_relat_1(A_62),C_63),C_63),A_62)
      | ~ r2_hidden(C_63,k2_relat_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_106,plain,(
    ! [C_69] : ~ r2_hidden(C_69,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_87,c_65])).

tff(c_114,plain,(
    ! [A_39] :
      ( ~ r2_hidden(A_39,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_106])).

tff(c_118,plain,(
    ! [A_39] : ~ r2_hidden(A_39,k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_114])).

tff(c_514,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_456,c_118])).

tff(c_548,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_514])).

tff(c_549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_548])).

tff(c_550,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_684,plain,(
    ! [A_127,B_128] :
      ( r2_hidden(k4_tarski('#skF_2'(A_127,B_128),'#skF_1'(A_127,B_128)),A_127)
      | r2_hidden('#skF_3'(A_127,B_128),B_128)
      | k2_relat_1(A_127) = B_128 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_556,plain,(
    ! [A_94,B_95] :
      ( ~ r2_hidden(A_94,B_95)
      | ~ r1_xboole_0(k1_tarski(A_94),B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_561,plain,(
    ! [A_94] : ~ r2_hidden(A_94,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_556])).

tff(c_714,plain,(
    ! [B_129] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_129),B_129)
      | k2_relat_1(k1_xboole_0) = B_129 ) ),
    inference(resolution,[status(thm)],[c_684,c_561])).

tff(c_734,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_714,c_561])).

tff(c_743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_550,c_734])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:04:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.37  
% 2.38/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.37  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1 > #skF_5
% 2.68/1.37  
% 2.68/1.37  %Foreground sorts:
% 2.68/1.37  
% 2.68/1.37  
% 2.68/1.37  %Background operators:
% 2.68/1.37  
% 2.68/1.37  
% 2.68/1.37  %Foreground operators:
% 2.68/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.68/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.68/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.68/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.68/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.68/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.68/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.68/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.68/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.37  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.68/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.68/1.37  
% 2.68/1.39  tff(f_68, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.68/1.39  tff(f_55, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.68/1.39  tff(f_28, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.68/1.39  tff(f_43, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.68/1.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.68/1.39  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.68/1.39  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 2.68/1.39  tff(c_34, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.68/1.39  tff(c_50, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 2.68/1.39  tff(c_359, plain, (![A_86, B_87]: (r2_hidden(k4_tarski('#skF_2'(A_86, B_87), '#skF_1'(A_86, B_87)), A_86) | r2_hidden('#skF_3'(A_86, B_87), B_87) | k2_relat_1(A_86)=B_87)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.68/1.39  tff(c_4, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.68/1.39  tff(c_60, plain, (![A_47, B_48]: (~r2_hidden(A_47, B_48) | ~r1_xboole_0(k1_tarski(A_47), B_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.68/1.39  tff(c_65, plain, (![A_47]: (~r2_hidden(A_47, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_60])).
% 2.68/1.39  tff(c_456, plain, (![B_90]: (r2_hidden('#skF_3'(k1_xboole_0, B_90), B_90) | k2_relat_1(k1_xboole_0)=B_90)), inference(resolution, [status(thm)], [c_359, c_65])).
% 2.68/1.39  tff(c_517, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_456, c_65])).
% 2.68/1.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.68/1.39  tff(c_36, plain, (![A_43]: (v1_relat_1(A_43) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.68/1.39  tff(c_40, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_36])).
% 2.68/1.39  tff(c_32, plain, (![A_39, B_40]: (r2_hidden('#skF_5'(A_39, B_40), k2_relat_1(B_40)) | ~r2_hidden(A_39, k1_relat_1(B_40)) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.68/1.39  tff(c_87, plain, (![A_62, C_63]: (r2_hidden(k4_tarski('#skF_4'(A_62, k2_relat_1(A_62), C_63), C_63), A_62) | ~r2_hidden(C_63, k2_relat_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.68/1.39  tff(c_106, plain, (![C_69]: (~r2_hidden(C_69, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_87, c_65])).
% 2.68/1.39  tff(c_114, plain, (![A_39]: (~r2_hidden(A_39, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_106])).
% 2.68/1.39  tff(c_118, plain, (![A_39]: (~r2_hidden(A_39, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_114])).
% 2.68/1.39  tff(c_514, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_456, c_118])).
% 2.68/1.39  tff(c_548, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_517, c_514])).
% 2.68/1.39  tff(c_549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_548])).
% 2.68/1.39  tff(c_550, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 2.68/1.39  tff(c_684, plain, (![A_127, B_128]: (r2_hidden(k4_tarski('#skF_2'(A_127, B_128), '#skF_1'(A_127, B_128)), A_127) | r2_hidden('#skF_3'(A_127, B_128), B_128) | k2_relat_1(A_127)=B_128)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.68/1.39  tff(c_556, plain, (![A_94, B_95]: (~r2_hidden(A_94, B_95) | ~r1_xboole_0(k1_tarski(A_94), B_95))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.68/1.39  tff(c_561, plain, (![A_94]: (~r2_hidden(A_94, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_556])).
% 2.68/1.39  tff(c_714, plain, (![B_129]: (r2_hidden('#skF_3'(k1_xboole_0, B_129), B_129) | k2_relat_1(k1_xboole_0)=B_129)), inference(resolution, [status(thm)], [c_684, c_561])).
% 2.68/1.39  tff(c_734, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_714, c_561])).
% 2.68/1.39  tff(c_743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_550, c_734])).
% 2.68/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.39  
% 2.68/1.39  Inference rules
% 2.68/1.39  ----------------------
% 2.68/1.39  #Ref     : 0
% 2.68/1.39  #Sup     : 132
% 2.68/1.39  #Fact    : 0
% 2.68/1.39  #Define  : 0
% 2.68/1.39  #Split   : 3
% 2.68/1.39  #Chain   : 0
% 2.68/1.39  #Close   : 0
% 2.68/1.39  
% 2.68/1.39  Ordering : KBO
% 2.68/1.39  
% 2.68/1.39  Simplification rules
% 2.68/1.39  ----------------------
% 2.68/1.39  #Subsume      : 27
% 2.68/1.39  #Demod        : 35
% 2.68/1.39  #Tautology    : 28
% 2.68/1.39  #SimpNegUnit  : 4
% 2.68/1.39  #BackRed      : 15
% 2.68/1.39  
% 2.68/1.39  #Partial instantiations: 0
% 2.68/1.39  #Strategies tried      : 1
% 2.68/1.39  
% 2.68/1.39  Timing (in seconds)
% 2.68/1.39  ----------------------
% 2.68/1.39  Preprocessing        : 0.32
% 2.68/1.39  Parsing              : 0.17
% 2.68/1.39  CNF conversion       : 0.02
% 2.68/1.39  Main loop            : 0.29
% 2.68/1.39  Inferencing          : 0.11
% 2.68/1.39  Reduction            : 0.08
% 2.68/1.39  Demodulation         : 0.05
% 2.68/1.39  BG Simplification    : 0.02
% 2.68/1.39  Subsumption          : 0.05
% 2.68/1.39  Abstraction          : 0.02
% 2.68/1.39  MUC search           : 0.00
% 2.68/1.39  Cooper               : 0.00
% 2.68/1.39  Total                : 0.64
% 2.68/1.39  Index Insertion      : 0.00
% 2.68/1.39  Index Deletion       : 0.00
% 2.68/1.39  Index Matching       : 0.00
% 2.68/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
