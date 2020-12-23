%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:27 EST 2020

% Result     : Theorem 4.03s
% Output     : CNFRefutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :   64 (  89 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 163 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
         => ( r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_42,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    r2_hidden(k4_tarski('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_774,plain,(
    ! [B_158,C_159,A_160] :
      ( r2_hidden(B_158,k2_relat_1(C_159))
      | ~ r2_hidden(k4_tarski(A_160,B_158),C_159)
      | ~ v1_relat_1(C_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_819,plain,
    ( r2_hidden('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_774])).

tff(c_833,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_819])).

tff(c_14,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_640,plain,(
    ! [A_129,B_130,C_131] :
      ( r1_tarski(k2_tarski(A_129,B_130),C_131)
      | ~ r2_hidden(B_130,C_131)
      | ~ r2_hidden(A_129,C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_649,plain,(
    ! [A_14,C_131] :
      ( r1_tarski(k1_tarski(A_14),C_131)
      | ~ r2_hidden(A_14,C_131)
      | ~ r2_hidden(A_14,C_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_640])).

tff(c_22,plain,(
    ! [A_18] :
      ( k2_xboole_0(k1_relat_1(A_18),k2_relat_1(A_18)) = k3_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_518,plain,(
    ! [A_112,C_113,B_114] :
      ( r2_hidden(A_112,k1_relat_1(C_113))
      | ~ r2_hidden(k4_tarski(A_112,B_114),C_113)
      | ~ v1_relat_1(C_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_548,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_518])).

tff(c_558,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_548])).

tff(c_12,plain,(
    ! [A_12,B_13] : k2_xboole_0(k1_tarski(A_12),k1_tarski(B_13)) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_897,plain,(
    ! [A_173,C_174,B_175,D_176] :
      ( r1_tarski(k2_xboole_0(A_173,C_174),k2_xboole_0(B_175,D_176))
      | ~ r1_tarski(C_174,D_176)
      | ~ r1_tarski(A_173,B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1068,plain,(
    ! [A_204,B_205,B_206,D_207] :
      ( r1_tarski(k2_tarski(A_204,B_205),k2_xboole_0(B_206,D_207))
      | ~ r1_tarski(k1_tarski(B_205),D_207)
      | ~ r1_tarski(k1_tarski(A_204),B_206) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_897])).

tff(c_18,plain,(
    ! [B_16,C_17,A_15] :
      ( r2_hidden(B_16,C_17)
      | ~ r1_tarski(k2_tarski(A_15,B_16),C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1766,plain,(
    ! [B_326,B_327,D_328,A_329] :
      ( r2_hidden(B_326,k2_xboole_0(B_327,D_328))
      | ~ r1_tarski(k1_tarski(B_326),D_328)
      | ~ r1_tarski(k1_tarski(A_329),B_327) ) ),
    inference(resolution,[status(thm)],[c_1068,c_18])).

tff(c_1911,plain,(
    ! [B_354,C_355,D_356,A_357] :
      ( r2_hidden(B_354,k2_xboole_0(C_355,D_356))
      | ~ r1_tarski(k1_tarski(B_354),D_356)
      | ~ r2_hidden(A_357,C_355) ) ),
    inference(resolution,[status(thm)],[c_649,c_1766])).

tff(c_2148,plain,(
    ! [B_367,D_368] :
      ( r2_hidden(B_367,k2_xboole_0(k1_relat_1('#skF_4'),D_368))
      | ~ r1_tarski(k1_tarski(B_367),D_368) ) ),
    inference(resolution,[status(thm)],[c_558,c_1911])).

tff(c_2168,plain,(
    ! [B_367] :
      ( r2_hidden(B_367,k3_relat_1('#skF_4'))
      | ~ r1_tarski(k1_tarski(B_367),k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2148])).

tff(c_2204,plain,(
    ! [B_372] :
      ( r2_hidden(B_372,k3_relat_1('#skF_4'))
      | ~ r1_tarski(k1_tarski(B_372),k2_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2168])).

tff(c_2210,plain,(
    ! [A_373] :
      ( r2_hidden(A_373,k3_relat_1('#skF_4'))
      | ~ r2_hidden(A_373,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_649,c_2204])).

tff(c_28,plain,
    ( ~ r2_hidden('#skF_3',k3_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_65,plain,(
    ~ r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_121,plain,(
    ! [A_53] :
      ( k2_xboole_0(k1_relat_1(A_53),k2_relat_1(A_53)) = k3_relat_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_127,plain,(
    ! [A_53] :
      ( r1_tarski(k1_relat_1(A_53),k3_relat_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_10])).

tff(c_310,plain,(
    ! [A_82,C_83,B_84] :
      ( r2_hidden(A_82,k1_relat_1(C_83))
      | ~ r2_hidden(k4_tarski(A_82,B_84),C_83)
      | ~ v1_relat_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_344,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_310])).

tff(c_355,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_344])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_359,plain,(
    ! [B_85] :
      ( r2_hidden('#skF_2',B_85)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_85) ) ),
    inference(resolution,[status(thm)],[c_355,c_2])).

tff(c_363,plain,
    ( r2_hidden('#skF_2',k3_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_127,c_359])).

tff(c_374,plain,(
    r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_363])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_374])).

tff(c_377,plain,(
    ~ r2_hidden('#skF_3',k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_2225,plain,(
    ~ r2_hidden('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2210,c_377])).

tff(c_2237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_2225])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.03/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.77  
% 4.03/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.77  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.03/1.77  
% 4.03/1.77  %Foreground sorts:
% 4.03/1.77  
% 4.03/1.77  
% 4.03/1.77  %Background operators:
% 4.03/1.77  
% 4.03/1.77  
% 4.03/1.77  %Foreground operators:
% 4.03/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.03/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.03/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.03/1.77  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.03/1.77  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 4.03/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.03/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.03/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.03/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.03/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.03/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.03/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.03/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.03/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.03/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.03/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.03/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.03/1.77  
% 4.40/1.78  tff(f_71, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 4.40/1.78  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 4.40/1.78  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.40/1.78  tff(f_50, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.40/1.78  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 4.40/1.78  tff(f_42, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 4.40/1.78  tff(f_38, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 4.40/1.78  tff(f_40, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.40/1.78  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.40/1.78  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.40/1.78  tff(c_30, plain, (r2_hidden(k4_tarski('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.40/1.78  tff(c_774, plain, (![B_158, C_159, A_160]: (r2_hidden(B_158, k2_relat_1(C_159)) | ~r2_hidden(k4_tarski(A_160, B_158), C_159) | ~v1_relat_1(C_159))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.40/1.78  tff(c_819, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_774])).
% 4.40/1.78  tff(c_833, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_819])).
% 4.40/1.78  tff(c_14, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.40/1.78  tff(c_640, plain, (![A_129, B_130, C_131]: (r1_tarski(k2_tarski(A_129, B_130), C_131) | ~r2_hidden(B_130, C_131) | ~r2_hidden(A_129, C_131))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.40/1.78  tff(c_649, plain, (![A_14, C_131]: (r1_tarski(k1_tarski(A_14), C_131) | ~r2_hidden(A_14, C_131) | ~r2_hidden(A_14, C_131))), inference(superposition, [status(thm), theory('equality')], [c_14, c_640])).
% 4.40/1.78  tff(c_22, plain, (![A_18]: (k2_xboole_0(k1_relat_1(A_18), k2_relat_1(A_18))=k3_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.40/1.78  tff(c_518, plain, (![A_112, C_113, B_114]: (r2_hidden(A_112, k1_relat_1(C_113)) | ~r2_hidden(k4_tarski(A_112, B_114), C_113) | ~v1_relat_1(C_113))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.40/1.78  tff(c_548, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_518])).
% 4.40/1.78  tff(c_558, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_548])).
% 4.40/1.78  tff(c_12, plain, (![A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(B_13))=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.40/1.78  tff(c_897, plain, (![A_173, C_174, B_175, D_176]: (r1_tarski(k2_xboole_0(A_173, C_174), k2_xboole_0(B_175, D_176)) | ~r1_tarski(C_174, D_176) | ~r1_tarski(A_173, B_175))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.40/1.78  tff(c_1068, plain, (![A_204, B_205, B_206, D_207]: (r1_tarski(k2_tarski(A_204, B_205), k2_xboole_0(B_206, D_207)) | ~r1_tarski(k1_tarski(B_205), D_207) | ~r1_tarski(k1_tarski(A_204), B_206))), inference(superposition, [status(thm), theory('equality')], [c_12, c_897])).
% 4.40/1.78  tff(c_18, plain, (![B_16, C_17, A_15]: (r2_hidden(B_16, C_17) | ~r1_tarski(k2_tarski(A_15, B_16), C_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.40/1.78  tff(c_1766, plain, (![B_326, B_327, D_328, A_329]: (r2_hidden(B_326, k2_xboole_0(B_327, D_328)) | ~r1_tarski(k1_tarski(B_326), D_328) | ~r1_tarski(k1_tarski(A_329), B_327))), inference(resolution, [status(thm)], [c_1068, c_18])).
% 4.40/1.78  tff(c_1911, plain, (![B_354, C_355, D_356, A_357]: (r2_hidden(B_354, k2_xboole_0(C_355, D_356)) | ~r1_tarski(k1_tarski(B_354), D_356) | ~r2_hidden(A_357, C_355))), inference(resolution, [status(thm)], [c_649, c_1766])).
% 4.40/1.78  tff(c_2148, plain, (![B_367, D_368]: (r2_hidden(B_367, k2_xboole_0(k1_relat_1('#skF_4'), D_368)) | ~r1_tarski(k1_tarski(B_367), D_368))), inference(resolution, [status(thm)], [c_558, c_1911])).
% 4.40/1.78  tff(c_2168, plain, (![B_367]: (r2_hidden(B_367, k3_relat_1('#skF_4')) | ~r1_tarski(k1_tarski(B_367), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2148])).
% 4.40/1.78  tff(c_2204, plain, (![B_372]: (r2_hidden(B_372, k3_relat_1('#skF_4')) | ~r1_tarski(k1_tarski(B_372), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2168])).
% 4.40/1.78  tff(c_2210, plain, (![A_373]: (r2_hidden(A_373, k3_relat_1('#skF_4')) | ~r2_hidden(A_373, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_649, c_2204])).
% 4.40/1.78  tff(c_28, plain, (~r2_hidden('#skF_3', k3_relat_1('#skF_4')) | ~r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.40/1.78  tff(c_65, plain, (~r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_28])).
% 4.40/1.78  tff(c_121, plain, (![A_53]: (k2_xboole_0(k1_relat_1(A_53), k2_relat_1(A_53))=k3_relat_1(A_53) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.40/1.78  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.40/1.78  tff(c_127, plain, (![A_53]: (r1_tarski(k1_relat_1(A_53), k3_relat_1(A_53)) | ~v1_relat_1(A_53))), inference(superposition, [status(thm), theory('equality')], [c_121, c_10])).
% 4.40/1.78  tff(c_310, plain, (![A_82, C_83, B_84]: (r2_hidden(A_82, k1_relat_1(C_83)) | ~r2_hidden(k4_tarski(A_82, B_84), C_83) | ~v1_relat_1(C_83))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.40/1.78  tff(c_344, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_310])).
% 4.40/1.78  tff(c_355, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_344])).
% 4.40/1.78  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.40/1.78  tff(c_359, plain, (![B_85]: (r2_hidden('#skF_2', B_85) | ~r1_tarski(k1_relat_1('#skF_4'), B_85))), inference(resolution, [status(thm)], [c_355, c_2])).
% 4.40/1.78  tff(c_363, plain, (r2_hidden('#skF_2', k3_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_127, c_359])).
% 4.40/1.78  tff(c_374, plain, (r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_363])).
% 4.40/1.78  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_374])).
% 4.40/1.78  tff(c_377, plain, (~r2_hidden('#skF_3', k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_28])).
% 4.40/1.78  tff(c_2225, plain, (~r2_hidden('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2210, c_377])).
% 4.40/1.78  tff(c_2237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_833, c_2225])).
% 4.40/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/1.78  
% 4.40/1.78  Inference rules
% 4.40/1.78  ----------------------
% 4.40/1.78  #Ref     : 0
% 4.40/1.78  #Sup     : 520
% 4.40/1.78  #Fact    : 0
% 4.40/1.78  #Define  : 0
% 4.40/1.78  #Split   : 1
% 4.40/1.78  #Chain   : 0
% 4.40/1.78  #Close   : 0
% 4.40/1.78  
% 4.40/1.78  Ordering : KBO
% 4.40/1.78  
% 4.40/1.78  Simplification rules
% 4.40/1.78  ----------------------
% 4.40/1.78  #Subsume      : 64
% 4.40/1.78  #Demod        : 64
% 4.40/1.79  #Tautology    : 64
% 4.40/1.79  #SimpNegUnit  : 1
% 4.40/1.79  #BackRed      : 0
% 4.40/1.79  
% 4.40/1.79  #Partial instantiations: 0
% 4.40/1.79  #Strategies tried      : 1
% 4.40/1.79  
% 4.40/1.79  Timing (in seconds)
% 4.40/1.79  ----------------------
% 4.40/1.79  Preprocessing        : 0.30
% 4.40/1.79  Parsing              : 0.16
% 4.40/1.79  CNF conversion       : 0.02
% 4.40/1.79  Main loop            : 0.72
% 4.40/1.79  Inferencing          : 0.27
% 4.40/1.79  Reduction            : 0.21
% 4.40/1.79  Demodulation         : 0.15
% 4.40/1.79  BG Simplification    : 0.02
% 4.40/1.79  Subsumption          : 0.15
% 4.40/1.79  Abstraction          : 0.03
% 4.40/1.79  MUC search           : 0.00
% 4.40/1.79  Cooper               : 0.00
% 4.40/1.79  Total                : 1.05
% 4.40/1.79  Index Insertion      : 0.00
% 4.40/1.79  Index Deletion       : 0.00
% 4.40/1.79  Index Matching       : 0.00
% 4.40/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
