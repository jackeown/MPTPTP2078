%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:44 EST 2020

% Result     : Theorem 33.72s
% Output     : CNFRefutation 33.72s
% Verified   : 
% Statistics : Number of formulae       :   73 (  95 expanded)
%              Number of leaves         :   30 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 ( 210 expanded)
%              Number of equality atoms :   22 (  34 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,(
    r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_152,plain,(
    ! [C_50,B_51,A_52] :
      ( r2_hidden(C_50,B_51)
      | ~ r2_hidden(C_50,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_233,plain,(
    ! [A_71,B_72,B_73] :
      ( r2_hidden('#skF_1'(A_71,B_72),B_73)
      | ~ r1_tarski(A_71,B_73)
      | r1_tarski(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_152])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2136,plain,(
    ! [A_224,B_225,B_226,B_227] :
      ( r2_hidden('#skF_1'(A_224,B_225),B_226)
      | ~ r1_tarski(B_227,B_226)
      | ~ r1_tarski(A_224,B_227)
      | r1_tarski(A_224,B_225) ) ),
    inference(resolution,[status(thm)],[c_233,c_2])).

tff(c_2182,plain,(
    ! [A_228,B_229] :
      ( r2_hidden('#skF_1'(A_228,B_229),k2_relat_1('#skF_5'))
      | ~ r1_tarski(A_228,'#skF_4')
      | r1_tarski(A_228,B_229) ) ),
    inference(resolution,[status(thm)],[c_50,c_2136])).

tff(c_2195,plain,(
    ! [A_228,B_229,B_2] :
      ( r2_hidden('#skF_1'(A_228,B_229),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_2)
      | ~ r1_tarski(A_228,'#skF_4')
      | r1_tarski(A_228,B_229) ) ),
    inference(resolution,[status(thm)],[c_2182,c_2])).

tff(c_54,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_156,plain,(
    ! [B_53,A_54] :
      ( k7_relat_1(B_53,A_54) = B_53
      | ~ r1_tarski(k1_relat_1(B_53),A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_162,plain,(
    ! [B_55] :
      ( k7_relat_1(B_55,k1_relat_1(B_55)) = B_55
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_12,c_156])).

tff(c_32,plain,(
    ! [B_20,A_19] :
      ( k2_relat_1(k7_relat_1(B_20,A_19)) = k9_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_168,plain,(
    ! [B_55] :
      ( k9_relat_1(B_55,k1_relat_1(B_55)) = k2_relat_1(B_55)
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_32])).

tff(c_816,plain,(
    ! [A_138,B_139,C_140] :
      ( r2_hidden(k4_tarski('#skF_2'(A_138,B_139,C_140),A_138),C_140)
      | ~ r2_hidden(A_138,k9_relat_1(C_140,B_139))
      | ~ v1_relat_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_42,plain,(
    ! [B_28,C_29,A_27] :
      ( r2_hidden(B_28,k2_relat_1(C_29))
      | ~ r2_hidden(k4_tarski(A_27,B_28),C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_868,plain,(
    ! [A_141,C_142,B_143] :
      ( r2_hidden(A_141,k2_relat_1(C_142))
      | ~ r2_hidden(A_141,k9_relat_1(C_142,B_143))
      | ~ v1_relat_1(C_142) ) ),
    inference(resolution,[status(thm)],[c_816,c_42])).

tff(c_16364,plain,(
    ! [C_785,B_786,B_787] :
      ( r2_hidden('#skF_1'(k9_relat_1(C_785,B_786),B_787),k2_relat_1(C_785))
      | ~ v1_relat_1(C_785)
      | r1_tarski(k9_relat_1(C_785,B_786),B_787) ) ),
    inference(resolution,[status(thm)],[c_6,c_868])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16425,plain,(
    ! [C_788,B_789] :
      ( ~ v1_relat_1(C_788)
      | r1_tarski(k9_relat_1(C_788,B_789),k2_relat_1(C_788)) ) ),
    inference(resolution,[status(thm)],[c_16364,c_4])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16706,plain,(
    ! [C_796,B_797] :
      ( k9_relat_1(C_796,B_797) = k2_relat_1(C_796)
      | ~ r1_tarski(k2_relat_1(C_796),k9_relat_1(C_796,B_797))
      | ~ v1_relat_1(C_796) ) ),
    inference(resolution,[status(thm)],[c_16425,c_8])).

tff(c_16747,plain,(
    ! [B_55] :
      ( k9_relat_1(B_55,k1_relat_1(B_55)) = k2_relat_1(B_55)
      | ~ r1_tarski(k2_relat_1(B_55),k2_relat_1(B_55))
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_16706])).

tff(c_16756,plain,(
    ! [B_55] :
      ( k9_relat_1(B_55,k1_relat_1(B_55)) = k2_relat_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16747])).

tff(c_18,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_90,plain,(
    ! [A_36,B_37] : ~ r2_hidden(A_36,k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_93,plain,(
    ! [A_9] : ~ r2_hidden(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_90])).

tff(c_48,plain,(
    k10_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden(k4_tarski('#skF_2'(A_13,B_14,C_15),A_13),C_15)
      | ~ r2_hidden(A_13,k9_relat_1(C_15,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1183,plain,(
    ! [A_166,C_167,B_168,D_169] :
      ( r2_hidden(A_166,k10_relat_1(C_167,B_168))
      | ~ r2_hidden(D_169,B_168)
      | ~ r2_hidden(k4_tarski(A_166,D_169),C_167)
      | ~ r2_hidden(D_169,k2_relat_1(C_167))
      | ~ v1_relat_1(C_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4710,plain,(
    ! [A_351,C_352,A_353,B_354] :
      ( r2_hidden(A_351,k10_relat_1(C_352,A_353))
      | ~ r2_hidden(k4_tarski(A_351,'#skF_1'(A_353,B_354)),C_352)
      | ~ r2_hidden('#skF_1'(A_353,B_354),k2_relat_1(C_352))
      | ~ v1_relat_1(C_352)
      | r1_tarski(A_353,B_354) ) ),
    inference(resolution,[status(thm)],[c_6,c_1183])).

tff(c_81944,plain,(
    ! [A_2021,B_2022,B_2023,C_2024] :
      ( r2_hidden('#skF_2'('#skF_1'(A_2021,B_2022),B_2023,C_2024),k10_relat_1(C_2024,A_2021))
      | ~ r2_hidden('#skF_1'(A_2021,B_2022),k2_relat_1(C_2024))
      | r1_tarski(A_2021,B_2022)
      | ~ r2_hidden('#skF_1'(A_2021,B_2022),k9_relat_1(C_2024,B_2023))
      | ~ v1_relat_1(C_2024) ) ),
    inference(resolution,[status(thm)],[c_28,c_4710])).

tff(c_82152,plain,(
    ! [B_2022,B_2023] :
      ( r2_hidden('#skF_2'('#skF_1'('#skF_4',B_2022),B_2023,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'('#skF_4',B_2022),k2_relat_1('#skF_5'))
      | r1_tarski('#skF_4',B_2022)
      | ~ r2_hidden('#skF_1'('#skF_4',B_2022),k9_relat_1('#skF_5',B_2023))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_81944])).

tff(c_82221,plain,(
    ! [B_2022,B_2023] :
      ( r2_hidden('#skF_2'('#skF_1'('#skF_4',B_2022),B_2023,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden('#skF_1'('#skF_4',B_2022),k2_relat_1('#skF_5'))
      | r1_tarski('#skF_4',B_2022)
      | ~ r2_hidden('#skF_1'('#skF_4',B_2022),k9_relat_1('#skF_5',B_2023)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_82152])).

tff(c_82223,plain,(
    ! [B_2025,B_2026] :
      ( ~ r2_hidden('#skF_1'('#skF_4',B_2025),k2_relat_1('#skF_5'))
      | r1_tarski('#skF_4',B_2025)
      | ~ r2_hidden('#skF_1'('#skF_4',B_2025),k9_relat_1('#skF_5',B_2026)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_82221])).

tff(c_82271,plain,(
    ! [B_2025] :
      ( ~ r2_hidden('#skF_1'('#skF_4',B_2025),k2_relat_1('#skF_5'))
      | r1_tarski('#skF_4',B_2025)
      | ~ r2_hidden('#skF_1'('#skF_4',B_2025),k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16756,c_82223])).

tff(c_82365,plain,(
    ! [B_2027] :
      ( r1_tarski('#skF_4',B_2027)
      | ~ r2_hidden('#skF_1'('#skF_4',B_2027),k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_82271])).

tff(c_82369,plain,(
    ! [B_229] :
      ( ~ r1_tarski(k2_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ r1_tarski('#skF_4','#skF_4')
      | r1_tarski('#skF_4',B_229) ) ),
    inference(resolution,[status(thm)],[c_2195,c_82365])).

tff(c_82389,plain,(
    ! [B_2028] : r1_tarski('#skF_4',B_2028) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_82369])).

tff(c_14,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82714,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_82389,c_14])).

tff(c_82854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_82714])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 33.72/25.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 33.72/25.32  
% 33.72/25.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 33.72/25.33  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 33.72/25.33  
% 33.72/25.33  %Foreground sorts:
% 33.72/25.33  
% 33.72/25.33  
% 33.72/25.33  %Background operators:
% 33.72/25.33  
% 33.72/25.33  
% 33.72/25.33  %Foreground operators:
% 33.72/25.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 33.72/25.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 33.72/25.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 33.72/25.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 33.72/25.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 33.72/25.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 33.72/25.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 33.72/25.33  tff('#skF_5', type, '#skF_5': $i).
% 33.72/25.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 33.72/25.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 33.72/25.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 33.72/25.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 33.72/25.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 33.72/25.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 33.72/25.33  tff('#skF_4', type, '#skF_4': $i).
% 33.72/25.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 33.72/25.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 33.72/25.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 33.72/25.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 33.72/25.33  
% 33.72/25.34  tff(f_102, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 33.72/25.34  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 33.72/25.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 33.72/25.34  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 33.72/25.34  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 33.72/25.34  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 33.72/25.34  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 33.72/25.34  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 33.72/25.34  tff(f_51, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 33.72/25.34  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 33.72/25.34  tff(f_42, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 33.72/25.34  tff(c_52, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 33.72/25.34  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 33.72/25.34  tff(c_50, plain, (r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 33.72/25.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 33.72/25.34  tff(c_152, plain, (![C_50, B_51, A_52]: (r2_hidden(C_50, B_51) | ~r2_hidden(C_50, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 33.72/25.34  tff(c_233, plain, (![A_71, B_72, B_73]: (r2_hidden('#skF_1'(A_71, B_72), B_73) | ~r1_tarski(A_71, B_73) | r1_tarski(A_71, B_72))), inference(resolution, [status(thm)], [c_6, c_152])).
% 33.72/25.34  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 33.72/25.34  tff(c_2136, plain, (![A_224, B_225, B_226, B_227]: (r2_hidden('#skF_1'(A_224, B_225), B_226) | ~r1_tarski(B_227, B_226) | ~r1_tarski(A_224, B_227) | r1_tarski(A_224, B_225))), inference(resolution, [status(thm)], [c_233, c_2])).
% 33.72/25.34  tff(c_2182, plain, (![A_228, B_229]: (r2_hidden('#skF_1'(A_228, B_229), k2_relat_1('#skF_5')) | ~r1_tarski(A_228, '#skF_4') | r1_tarski(A_228, B_229))), inference(resolution, [status(thm)], [c_50, c_2136])).
% 33.72/25.34  tff(c_2195, plain, (![A_228, B_229, B_2]: (r2_hidden('#skF_1'(A_228, B_229), B_2) | ~r1_tarski(k2_relat_1('#skF_5'), B_2) | ~r1_tarski(A_228, '#skF_4') | r1_tarski(A_228, B_229))), inference(resolution, [status(thm)], [c_2182, c_2])).
% 33.72/25.34  tff(c_54, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 33.72/25.34  tff(c_156, plain, (![B_53, A_54]: (k7_relat_1(B_53, A_54)=B_53 | ~r1_tarski(k1_relat_1(B_53), A_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_91])).
% 33.72/25.34  tff(c_162, plain, (![B_55]: (k7_relat_1(B_55, k1_relat_1(B_55))=B_55 | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_12, c_156])).
% 33.72/25.34  tff(c_32, plain, (![B_20, A_19]: (k2_relat_1(k7_relat_1(B_20, A_19))=k9_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 33.72/25.34  tff(c_168, plain, (![B_55]: (k9_relat_1(B_55, k1_relat_1(B_55))=k2_relat_1(B_55) | ~v1_relat_1(B_55) | ~v1_relat_1(B_55))), inference(superposition, [status(thm), theory('equality')], [c_162, c_32])).
% 33.72/25.34  tff(c_816, plain, (![A_138, B_139, C_140]: (r2_hidden(k4_tarski('#skF_2'(A_138, B_139, C_140), A_138), C_140) | ~r2_hidden(A_138, k9_relat_1(C_140, B_139)) | ~v1_relat_1(C_140))), inference(cnfTransformation, [status(thm)], [f_62])).
% 33.72/25.34  tff(c_42, plain, (![B_28, C_29, A_27]: (r2_hidden(B_28, k2_relat_1(C_29)) | ~r2_hidden(k4_tarski(A_27, B_28), C_29) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_85])).
% 33.72/25.34  tff(c_868, plain, (![A_141, C_142, B_143]: (r2_hidden(A_141, k2_relat_1(C_142)) | ~r2_hidden(A_141, k9_relat_1(C_142, B_143)) | ~v1_relat_1(C_142))), inference(resolution, [status(thm)], [c_816, c_42])).
% 33.72/25.34  tff(c_16364, plain, (![C_785, B_786, B_787]: (r2_hidden('#skF_1'(k9_relat_1(C_785, B_786), B_787), k2_relat_1(C_785)) | ~v1_relat_1(C_785) | r1_tarski(k9_relat_1(C_785, B_786), B_787))), inference(resolution, [status(thm)], [c_6, c_868])).
% 33.72/25.34  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 33.72/25.34  tff(c_16425, plain, (![C_788, B_789]: (~v1_relat_1(C_788) | r1_tarski(k9_relat_1(C_788, B_789), k2_relat_1(C_788)))), inference(resolution, [status(thm)], [c_16364, c_4])).
% 33.72/25.34  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 33.72/25.34  tff(c_16706, plain, (![C_796, B_797]: (k9_relat_1(C_796, B_797)=k2_relat_1(C_796) | ~r1_tarski(k2_relat_1(C_796), k9_relat_1(C_796, B_797)) | ~v1_relat_1(C_796))), inference(resolution, [status(thm)], [c_16425, c_8])).
% 33.72/25.34  tff(c_16747, plain, (![B_55]: (k9_relat_1(B_55, k1_relat_1(B_55))=k2_relat_1(B_55) | ~r1_tarski(k2_relat_1(B_55), k2_relat_1(B_55)) | ~v1_relat_1(B_55) | ~v1_relat_1(B_55) | ~v1_relat_1(B_55))), inference(superposition, [status(thm), theory('equality')], [c_168, c_16706])).
% 33.72/25.34  tff(c_16756, plain, (![B_55]: (k9_relat_1(B_55, k1_relat_1(B_55))=k2_relat_1(B_55) | ~v1_relat_1(B_55))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16747])).
% 33.72/25.34  tff(c_18, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 33.72/25.34  tff(c_90, plain, (![A_36, B_37]: (~r2_hidden(A_36, k2_zfmisc_1(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 33.72/25.34  tff(c_93, plain, (![A_9]: (~r2_hidden(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_90])).
% 33.72/25.34  tff(c_48, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 33.72/25.34  tff(c_28, plain, (![A_13, B_14, C_15]: (r2_hidden(k4_tarski('#skF_2'(A_13, B_14, C_15), A_13), C_15) | ~r2_hidden(A_13, k9_relat_1(C_15, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 33.72/25.34  tff(c_1183, plain, (![A_166, C_167, B_168, D_169]: (r2_hidden(A_166, k10_relat_1(C_167, B_168)) | ~r2_hidden(D_169, B_168) | ~r2_hidden(k4_tarski(A_166, D_169), C_167) | ~r2_hidden(D_169, k2_relat_1(C_167)) | ~v1_relat_1(C_167))), inference(cnfTransformation, [status(thm)], [f_77])).
% 33.72/25.34  tff(c_4710, plain, (![A_351, C_352, A_353, B_354]: (r2_hidden(A_351, k10_relat_1(C_352, A_353)) | ~r2_hidden(k4_tarski(A_351, '#skF_1'(A_353, B_354)), C_352) | ~r2_hidden('#skF_1'(A_353, B_354), k2_relat_1(C_352)) | ~v1_relat_1(C_352) | r1_tarski(A_353, B_354))), inference(resolution, [status(thm)], [c_6, c_1183])).
% 33.72/25.34  tff(c_81944, plain, (![A_2021, B_2022, B_2023, C_2024]: (r2_hidden('#skF_2'('#skF_1'(A_2021, B_2022), B_2023, C_2024), k10_relat_1(C_2024, A_2021)) | ~r2_hidden('#skF_1'(A_2021, B_2022), k2_relat_1(C_2024)) | r1_tarski(A_2021, B_2022) | ~r2_hidden('#skF_1'(A_2021, B_2022), k9_relat_1(C_2024, B_2023)) | ~v1_relat_1(C_2024))), inference(resolution, [status(thm)], [c_28, c_4710])).
% 33.72/25.34  tff(c_82152, plain, (![B_2022, B_2023]: (r2_hidden('#skF_2'('#skF_1'('#skF_4', B_2022), B_2023, '#skF_5'), k1_xboole_0) | ~r2_hidden('#skF_1'('#skF_4', B_2022), k2_relat_1('#skF_5')) | r1_tarski('#skF_4', B_2022) | ~r2_hidden('#skF_1'('#skF_4', B_2022), k9_relat_1('#skF_5', B_2023)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_81944])).
% 33.72/25.34  tff(c_82221, plain, (![B_2022, B_2023]: (r2_hidden('#skF_2'('#skF_1'('#skF_4', B_2022), B_2023, '#skF_5'), k1_xboole_0) | ~r2_hidden('#skF_1'('#skF_4', B_2022), k2_relat_1('#skF_5')) | r1_tarski('#skF_4', B_2022) | ~r2_hidden('#skF_1'('#skF_4', B_2022), k9_relat_1('#skF_5', B_2023)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_82152])).
% 33.72/25.34  tff(c_82223, plain, (![B_2025, B_2026]: (~r2_hidden('#skF_1'('#skF_4', B_2025), k2_relat_1('#skF_5')) | r1_tarski('#skF_4', B_2025) | ~r2_hidden('#skF_1'('#skF_4', B_2025), k9_relat_1('#skF_5', B_2026)))), inference(negUnitSimplification, [status(thm)], [c_93, c_82221])).
% 33.72/25.34  tff(c_82271, plain, (![B_2025]: (~r2_hidden('#skF_1'('#skF_4', B_2025), k2_relat_1('#skF_5')) | r1_tarski('#skF_4', B_2025) | ~r2_hidden('#skF_1'('#skF_4', B_2025), k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16756, c_82223])).
% 33.72/25.34  tff(c_82365, plain, (![B_2027]: (r1_tarski('#skF_4', B_2027) | ~r2_hidden('#skF_1'('#skF_4', B_2027), k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_82271])).
% 33.72/25.34  tff(c_82369, plain, (![B_229]: (~r1_tarski(k2_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~r1_tarski('#skF_4', '#skF_4') | r1_tarski('#skF_4', B_229))), inference(resolution, [status(thm)], [c_2195, c_82365])).
% 33.72/25.34  tff(c_82389, plain, (![B_2028]: (r1_tarski('#skF_4', B_2028))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_82369])).
% 33.72/25.34  tff(c_14, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 33.72/25.34  tff(c_82714, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_82389, c_14])).
% 33.72/25.34  tff(c_82854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_82714])).
% 33.72/25.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 33.72/25.34  
% 33.72/25.34  Inference rules
% 33.72/25.34  ----------------------
% 33.72/25.34  #Ref     : 0
% 33.72/25.34  #Sup     : 20717
% 33.72/25.34  #Fact    : 0
% 33.72/25.34  #Define  : 0
% 33.72/25.34  #Split   : 39
% 33.72/25.34  #Chain   : 0
% 33.72/25.34  #Close   : 0
% 33.72/25.34  
% 33.72/25.34  Ordering : KBO
% 33.72/25.34  
% 33.72/25.34  Simplification rules
% 33.72/25.34  ----------------------
% 33.72/25.34  #Subsume      : 8494
% 33.72/25.34  #Demod        : 2133
% 33.72/25.34  #Tautology    : 1487
% 33.72/25.34  #SimpNegUnit  : 67
% 33.72/25.34  #BackRed      : 0
% 33.72/25.34  
% 33.72/25.34  #Partial instantiations: 0
% 33.72/25.34  #Strategies tried      : 1
% 33.72/25.34  
% 33.72/25.34  Timing (in seconds)
% 33.72/25.34  ----------------------
% 33.72/25.35  Preprocessing        : 0.31
% 33.72/25.35  Parsing              : 0.16
% 33.72/25.35  CNF conversion       : 0.02
% 33.72/25.35  Main loop            : 24.25
% 33.72/25.35  Inferencing          : 1.95
% 33.72/25.35  Reduction            : 2.23
% 33.72/25.35  Demodulation         : 1.42
% 33.72/25.35  BG Simplification    : 0.20
% 33.72/25.35  Subsumption          : 19.10
% 33.72/25.35  Abstraction          : 0.36
% 33.72/25.35  MUC search           : 0.00
% 33.72/25.35  Cooper               : 0.00
% 33.72/25.35  Total                : 24.60
% 33.72/25.35  Index Insertion      : 0.00
% 33.72/25.35  Index Deletion       : 0.00
% 33.72/25.35  Index Matching       : 0.00
% 33.72/25.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
