%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:15 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :   62 (  91 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 ( 125 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_2 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_28,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_4,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_2048,plain,(
    ! [A_201,C_202,B_203] :
      ( ~ r2_hidden(A_201,C_202)
      | ~ r1_xboole_0(k2_tarski(A_201,B_203),C_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2056,plain,(
    ! [A_201] : ~ r2_hidden(A_201,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_2048])).

tff(c_48,plain,
    ( k11_relat_1('#skF_10','#skF_9') = k1_xboole_0
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_80,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,
    ( r2_hidden('#skF_9',k1_relat_1('#skF_10'))
    | k11_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_81,plain,(
    k11_relat_1('#skF_10','#skF_9') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_54])).

tff(c_46,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_737,plain,(
    ! [A_143,B_144] :
      ( r2_hidden(k4_tarski('#skF_4'(A_143,B_144),'#skF_5'(A_143,B_144)),A_143)
      | r2_hidden('#skF_6'(A_143,B_144),B_144)
      | k1_relat_1(A_143) = B_144 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_82,plain,(
    ! [A_66,C_67,B_68] :
      ( ~ r2_hidden(A_66,C_67)
      | ~ r1_xboole_0(k2_tarski(A_66,B_68),C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    ! [A_66] : ~ r2_hidden(A_66,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_1079,plain,(
    ! [B_168] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_168),B_168)
      | k1_relat_1(k1_xboole_0) = B_168 ) ),
    inference(resolution,[status(thm)],[c_737,c_90])).

tff(c_1172,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1079,c_90])).

tff(c_814,plain,(
    ! [B_144] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_144),B_144)
      | k1_relat_1(k1_xboole_0) = B_144 ) ),
    inference(resolution,[status(thm)],[c_737,c_90])).

tff(c_1351,plain,(
    ! [B_176] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_176),B_176)
      | k1_xboole_0 = B_176 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1172,c_814])).

tff(c_122,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden(k4_tarski(A_78,B_79),C_80)
      | ~ r2_hidden(B_79,k11_relat_1(C_80,A_78))
      | ~ v1_relat_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    ! [C_44,A_29,D_47] :
      ( r2_hidden(C_44,k1_relat_1(A_29))
      | ~ r2_hidden(k4_tarski(C_44,D_47),A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_130,plain,(
    ! [A_78,C_80,B_79] :
      ( r2_hidden(A_78,k1_relat_1(C_80))
      | ~ r2_hidden(B_79,k11_relat_1(C_80,A_78))
      | ~ v1_relat_1(C_80) ) ),
    inference(resolution,[status(thm)],[c_122,c_22])).

tff(c_1977,plain,(
    ! [A_198,C_199] :
      ( r2_hidden(A_198,k1_relat_1(C_199))
      | ~ v1_relat_1(C_199)
      | k11_relat_1(C_199,A_198) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1351,c_130])).

tff(c_2008,plain,
    ( ~ v1_relat_1('#skF_10')
    | k11_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1977,c_80])).

tff(c_2028,plain,(
    k11_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2008])).

tff(c_2030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_2028])).

tff(c_2032,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2031,plain,(
    k11_relat_1('#skF_10','#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2233,plain,(
    ! [C_247,A_248] :
      ( r2_hidden(k4_tarski(C_247,'#skF_7'(A_248,k1_relat_1(A_248),C_247)),A_248)
      | ~ r2_hidden(C_247,k1_relat_1(A_248)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_44,plain,(
    ! [B_56,C_57,A_55] :
      ( r2_hidden(B_56,k11_relat_1(C_57,A_55))
      | ~ r2_hidden(k4_tarski(A_55,B_56),C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3757,plain,(
    ! [A_340,C_341] :
      ( r2_hidden('#skF_7'(A_340,k1_relat_1(A_340),C_341),k11_relat_1(A_340,C_341))
      | ~ v1_relat_1(A_340)
      | ~ r2_hidden(C_341,k1_relat_1(A_340)) ) ),
    inference(resolution,[status(thm)],[c_2233,c_44])).

tff(c_3773,plain,
    ( r2_hidden('#skF_7'('#skF_10',k1_relat_1('#skF_10'),'#skF_9'),k1_xboole_0)
    | ~ v1_relat_1('#skF_10')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2031,c_3757])).

tff(c_3783,plain,(
    r2_hidden('#skF_7'('#skF_10',k1_relat_1('#skF_10'),'#skF_9'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2032,c_46,c_3773])).

tff(c_3785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2056,c_3783])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.03/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.78  
% 4.03/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.78  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k11_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_2 > #skF_8 > #skF_5 > #skF_4
% 4.42/1.78  
% 4.42/1.78  %Foreground sorts:
% 4.42/1.78  
% 4.42/1.78  
% 4.42/1.78  %Background operators:
% 4.42/1.78  
% 4.42/1.78  
% 4.42/1.78  %Foreground operators:
% 4.42/1.78  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.42/1.78  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 4.42/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.42/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.42/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.42/1.78  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.42/1.78  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.42/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.42/1.78  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.42/1.78  tff('#skF_10', type, '#skF_10': $i).
% 4.42/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.42/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.42/1.78  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 4.42/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.42/1.78  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.42/1.78  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.42/1.78  tff('#skF_9', type, '#skF_9': $i).
% 4.42/1.78  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 4.42/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.42/1.78  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.42/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.42/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.42/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.42/1.78  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 4.42/1.78  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.42/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.42/1.78  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.42/1.78  
% 4.45/1.79  tff(f_28, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.45/1.79  tff(f_37, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 4.45/1.79  tff(f_89, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 4.45/1.79  tff(f_60, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 4.45/1.79  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 4.45/1.79  tff(c_4, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.45/1.79  tff(c_2048, plain, (![A_201, C_202, B_203]: (~r2_hidden(A_201, C_202) | ~r1_xboole_0(k2_tarski(A_201, B_203), C_202))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.45/1.79  tff(c_2056, plain, (![A_201]: (~r2_hidden(A_201, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_2048])).
% 4.45/1.79  tff(c_48, plain, (k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0 | ~r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.45/1.79  tff(c_80, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_48])).
% 4.45/1.79  tff(c_54, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10')) | k11_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.45/1.79  tff(c_81, plain, (k11_relat_1('#skF_10', '#skF_9')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_80, c_54])).
% 4.45/1.79  tff(c_46, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.45/1.79  tff(c_737, plain, (![A_143, B_144]: (r2_hidden(k4_tarski('#skF_4'(A_143, B_144), '#skF_5'(A_143, B_144)), A_143) | r2_hidden('#skF_6'(A_143, B_144), B_144) | k1_relat_1(A_143)=B_144)), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.45/1.79  tff(c_82, plain, (![A_66, C_67, B_68]: (~r2_hidden(A_66, C_67) | ~r1_xboole_0(k2_tarski(A_66, B_68), C_67))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.45/1.79  tff(c_90, plain, (![A_66]: (~r2_hidden(A_66, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_82])).
% 4.45/1.79  tff(c_1079, plain, (![B_168]: (r2_hidden('#skF_6'(k1_xboole_0, B_168), B_168) | k1_relat_1(k1_xboole_0)=B_168)), inference(resolution, [status(thm)], [c_737, c_90])).
% 4.45/1.79  tff(c_1172, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1079, c_90])).
% 4.45/1.79  tff(c_814, plain, (![B_144]: (r2_hidden('#skF_6'(k1_xboole_0, B_144), B_144) | k1_relat_1(k1_xboole_0)=B_144)), inference(resolution, [status(thm)], [c_737, c_90])).
% 4.45/1.79  tff(c_1351, plain, (![B_176]: (r2_hidden('#skF_6'(k1_xboole_0, B_176), B_176) | k1_xboole_0=B_176)), inference(demodulation, [status(thm), theory('equality')], [c_1172, c_814])).
% 4.45/1.79  tff(c_122, plain, (![A_78, B_79, C_80]: (r2_hidden(k4_tarski(A_78, B_79), C_80) | ~r2_hidden(B_79, k11_relat_1(C_80, A_78)) | ~v1_relat_1(C_80))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.45/1.79  tff(c_22, plain, (![C_44, A_29, D_47]: (r2_hidden(C_44, k1_relat_1(A_29)) | ~r2_hidden(k4_tarski(C_44, D_47), A_29))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.45/1.79  tff(c_130, plain, (![A_78, C_80, B_79]: (r2_hidden(A_78, k1_relat_1(C_80)) | ~r2_hidden(B_79, k11_relat_1(C_80, A_78)) | ~v1_relat_1(C_80))), inference(resolution, [status(thm)], [c_122, c_22])).
% 4.45/1.79  tff(c_1977, plain, (![A_198, C_199]: (r2_hidden(A_198, k1_relat_1(C_199)) | ~v1_relat_1(C_199) | k11_relat_1(C_199, A_198)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1351, c_130])).
% 4.45/1.79  tff(c_2008, plain, (~v1_relat_1('#skF_10') | k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_1977, c_80])).
% 4.45/1.79  tff(c_2028, plain, (k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2008])).
% 4.45/1.79  tff(c_2030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_2028])).
% 4.45/1.79  tff(c_2032, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_48])).
% 4.45/1.79  tff(c_2031, plain, (k11_relat_1('#skF_10', '#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 4.45/1.79  tff(c_2233, plain, (![C_247, A_248]: (r2_hidden(k4_tarski(C_247, '#skF_7'(A_248, k1_relat_1(A_248), C_247)), A_248) | ~r2_hidden(C_247, k1_relat_1(A_248)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.45/1.79  tff(c_44, plain, (![B_56, C_57, A_55]: (r2_hidden(B_56, k11_relat_1(C_57, A_55)) | ~r2_hidden(k4_tarski(A_55, B_56), C_57) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.45/1.79  tff(c_3757, plain, (![A_340, C_341]: (r2_hidden('#skF_7'(A_340, k1_relat_1(A_340), C_341), k11_relat_1(A_340, C_341)) | ~v1_relat_1(A_340) | ~r2_hidden(C_341, k1_relat_1(A_340)))), inference(resolution, [status(thm)], [c_2233, c_44])).
% 4.45/1.79  tff(c_3773, plain, (r2_hidden('#skF_7'('#skF_10', k1_relat_1('#skF_10'), '#skF_9'), k1_xboole_0) | ~v1_relat_1('#skF_10') | ~r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_2031, c_3757])).
% 4.45/1.79  tff(c_3783, plain, (r2_hidden('#skF_7'('#skF_10', k1_relat_1('#skF_10'), '#skF_9'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2032, c_46, c_3773])).
% 4.45/1.79  tff(c_3785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2056, c_3783])).
% 4.45/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.79  
% 4.45/1.79  Inference rules
% 4.45/1.79  ----------------------
% 4.45/1.79  #Ref     : 2
% 4.45/1.79  #Sup     : 709
% 4.45/1.79  #Fact    : 0
% 4.45/1.79  #Define  : 0
% 4.45/1.79  #Split   : 1
% 4.45/1.79  #Chain   : 0
% 4.45/1.79  #Close   : 0
% 4.45/1.79  
% 4.45/1.79  Ordering : KBO
% 4.45/1.79  
% 4.45/1.79  Simplification rules
% 4.45/1.79  ----------------------
% 4.45/1.79  #Subsume      : 175
% 4.45/1.79  #Demod        : 629
% 4.45/1.79  #Tautology    : 213
% 4.45/1.79  #SimpNegUnit  : 30
% 4.45/1.79  #BackRed      : 75
% 4.45/1.79  
% 4.45/1.79  #Partial instantiations: 0
% 4.45/1.79  #Strategies tried      : 1
% 4.45/1.79  
% 4.45/1.79  Timing (in seconds)
% 4.45/1.79  ----------------------
% 4.45/1.80  Preprocessing        : 0.31
% 4.45/1.80  Parsing              : 0.16
% 4.45/1.80  CNF conversion       : 0.02
% 4.45/1.80  Main loop            : 0.70
% 4.45/1.80  Inferencing          : 0.25
% 4.45/1.80  Reduction            : 0.23
% 4.45/1.80  Demodulation         : 0.16
% 4.45/1.80  BG Simplification    : 0.03
% 4.45/1.80  Subsumption          : 0.13
% 4.45/1.80  Abstraction          : 0.04
% 4.45/1.80  MUC search           : 0.00
% 4.45/1.80  Cooper               : 0.00
% 4.45/1.80  Total                : 1.04
% 4.45/1.80  Index Insertion      : 0.00
% 4.45/1.80  Index Deletion       : 0.00
% 4.45/1.80  Index Matching       : 0.00
% 4.45/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
