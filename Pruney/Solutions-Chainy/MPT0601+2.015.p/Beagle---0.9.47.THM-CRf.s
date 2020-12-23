%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:16 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 134 expanded)
%              Number of leaves         :   40 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  124 ( 223 expanded)
%              Number of equality atoms :   39 (  70 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_99,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_60,plain,
    ( r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_110,plain,(
    k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_44,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_24,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(k1_tarski(A_26),B_27)
      | r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_383,plain,(
    ! [A_102,B_103] :
      ( k7_relat_1(A_102,B_103) = k1_xboole_0
      | ~ r1_xboole_0(B_103,k1_relat_1(A_102))
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_536,plain,(
    ! [A_119,A_120] :
      ( k7_relat_1(A_119,k1_tarski(A_120)) = k1_xboole_0
      | ~ v1_relat_1(A_119)
      | r2_hidden(A_120,k1_relat_1(A_119)) ) ),
    inference(resolution,[status(thm)],[c_24,c_383])).

tff(c_54,plain,
    ( k11_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_142,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_54])).

tff(c_545,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_536,c_142])).

tff(c_553,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_545])).

tff(c_38,plain,(
    ! [B_39,A_38] :
      ( k2_relat_1(k7_relat_1(B_39,A_38)) = k9_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_563,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_3')) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_38])).

tff(c_572,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_563])).

tff(c_34,plain,(
    ! [A_33,B_35] :
      ( k9_relat_1(A_33,k1_tarski(B_35)) = k11_relat_1(A_33,B_35)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_579,plain,
    ( k11_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_34])).

tff(c_586,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_579])).

tff(c_588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_586])).

tff(c_589,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_922,plain,(
    ! [B_175,A_176] :
      ( r1_xboole_0(k1_relat_1(B_175),A_176)
      | k7_relat_1(B_175,A_176) != k1_xboole_0
      | ~ v1_relat_1(B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_xboole_0(B_7,A_6)
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1018,plain,(
    ! [A_184,B_185] :
      ( r1_xboole_0(A_184,k1_relat_1(B_185))
      | k7_relat_1(B_185,A_184) != k1_xboole_0
      | ~ v1_relat_1(B_185) ) ),
    inference(resolution,[status(thm)],[c_922,c_8])).

tff(c_14,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_644,plain,(
    ! [A_137,C_138,B_139] :
      ( ~ r2_hidden(A_137,C_138)
      | ~ r1_xboole_0(k2_tarski(A_137,B_139),C_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_651,plain,(
    ! [A_11,C_138] :
      ( ~ r2_hidden(A_11,C_138)
      | ~ r1_xboole_0(k1_tarski(A_11),C_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_644])).

tff(c_1118,plain,(
    ! [A_202,B_203] :
      ( ~ r2_hidden(A_202,k1_relat_1(B_203))
      | k7_relat_1(B_203,k1_tarski(A_202)) != k1_xboole_0
      | ~ v1_relat_1(B_203) ) ),
    inference(resolution,[status(thm)],[c_1018,c_651])).

tff(c_1140,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_3')) != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_589,c_1118])).

tff(c_1151,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1140])).

tff(c_36,plain,(
    ! [A_36,B_37] :
      ( v1_relat_1(k7_relat_1(A_36,B_37))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    ! [A_28] : k2_zfmisc_1(A_28,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_590,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_735,plain,(
    ! [B_154,A_155] :
      ( k2_relat_1(k7_relat_1(B_154,A_155)) = k9_relat_1(B_154,A_155)
      | ~ v1_relat_1(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    ! [A_43] :
      ( r1_tarski(A_43,k2_zfmisc_1(k1_relat_1(A_43),k2_relat_1(A_43)))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1322,plain,(
    ! [B_230,A_231] :
      ( r1_tarski(k7_relat_1(B_230,A_231),k2_zfmisc_1(k1_relat_1(k7_relat_1(B_230,A_231)),k9_relat_1(B_230,A_231)))
      | ~ v1_relat_1(k7_relat_1(B_230,A_231))
      | ~ v1_relat_1(B_230) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_735,c_42])).

tff(c_1634,plain,(
    ! [A_281,B_282] :
      ( r1_tarski(k7_relat_1(A_281,k1_tarski(B_282)),k2_zfmisc_1(k1_relat_1(k7_relat_1(A_281,k1_tarski(B_282))),k11_relat_1(A_281,B_282)))
      | ~ v1_relat_1(k7_relat_1(A_281,k1_tarski(B_282)))
      | ~ v1_relat_1(A_281)
      | ~ v1_relat_1(A_281) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1322])).

tff(c_1658,plain,
    ( r1_tarski(k7_relat_1('#skF_4',k1_tarski('#skF_3')),k2_zfmisc_1(k1_relat_1(k7_relat_1('#skF_4',k1_tarski('#skF_3'))),k1_xboole_0))
    | ~ v1_relat_1(k7_relat_1('#skF_4',k1_tarski('#skF_3')))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_590,c_1634])).

tff(c_1670,plain,
    ( r1_tarski(k7_relat_1('#skF_4',k1_tarski('#skF_3')),k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1('#skF_4',k1_tarski('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_28,c_1658])).

tff(c_1714,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4',k1_tarski('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1670])).

tff(c_1717,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1714])).

tff(c_1721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1717])).

tff(c_1722,plain,(
    r1_tarski(k7_relat_1('#skF_4',k1_tarski('#skF_3')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1670])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_671,plain,(
    ! [C_142,B_143,A_144] :
      ( r2_hidden(C_142,B_143)
      | ~ r2_hidden(C_142,A_144)
      | ~ r1_tarski(A_144,B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_756,plain,(
    ! [A_158,B_159] :
      ( r2_hidden('#skF_2'(A_158),B_159)
      | ~ r1_tarski(A_158,B_159)
      | k1_xboole_0 = A_158 ) ),
    inference(resolution,[status(thm)],[c_10,c_671])).

tff(c_12,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_657,plain,(
    ! [A_137] : ~ r2_hidden(A_137,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_644])).

tff(c_768,plain,(
    ! [A_158] :
      ( ~ r1_tarski(A_158,k1_xboole_0)
      | k1_xboole_0 = A_158 ) ),
    inference(resolution,[status(thm)],[c_756,c_657])).

tff(c_1736,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1722,c_768])).

tff(c_1747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1151,c_1736])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:14:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.63  
% 3.40/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.63  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.40/1.63  
% 3.40/1.63  %Foreground sorts:
% 3.40/1.63  
% 3.40/1.63  
% 3.40/1.63  %Background operators:
% 3.40/1.63  
% 3.40/1.63  
% 3.40/1.63  %Foreground operators:
% 3.40/1.63  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.40/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.40/1.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.40/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.40/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.40/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.40/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.40/1.63  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.40/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.40/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.40/1.63  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.40/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.63  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.40/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.40/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.40/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.40/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.40/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.40/1.63  
% 3.40/1.65  tff(f_113, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.40/1.65  tff(f_99, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.40/1.65  tff(f_61, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.40/1.65  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 3.40/1.65  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.40/1.65  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.40/1.65  tff(f_105, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 3.40/1.65  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.40/1.65  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.40/1.65  tff(f_72, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.40/1.65  tff(f_81, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.40/1.65  tff(f_67, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.40/1.65  tff(f_96, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.40/1.65  tff(f_44, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.40/1.65  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.40/1.65  tff(f_46, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.40/1.65  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.40/1.65  tff(c_60, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4')) | k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.40/1.65  tff(c_110, plain, (k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 3.40/1.65  tff(c_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.40/1.65  tff(c_24, plain, (![A_26, B_27]: (r1_xboole_0(k1_tarski(A_26), B_27) | r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.40/1.65  tff(c_383, plain, (![A_102, B_103]: (k7_relat_1(A_102, B_103)=k1_xboole_0 | ~r1_xboole_0(B_103, k1_relat_1(A_102)) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.40/1.65  tff(c_536, plain, (![A_119, A_120]: (k7_relat_1(A_119, k1_tarski(A_120))=k1_xboole_0 | ~v1_relat_1(A_119) | r2_hidden(A_120, k1_relat_1(A_119)))), inference(resolution, [status(thm)], [c_24, c_383])).
% 3.40/1.65  tff(c_54, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.40/1.65  tff(c_142, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_110, c_54])).
% 3.40/1.65  tff(c_545, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_536, c_142])).
% 3.40/1.65  tff(c_553, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_545])).
% 3.40/1.65  tff(c_38, plain, (![B_39, A_38]: (k2_relat_1(k7_relat_1(B_39, A_38))=k9_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.40/1.65  tff(c_563, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_3'))=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_553, c_38])).
% 3.40/1.65  tff(c_572, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_563])).
% 3.40/1.65  tff(c_34, plain, (![A_33, B_35]: (k9_relat_1(A_33, k1_tarski(B_35))=k11_relat_1(A_33, B_35) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.40/1.65  tff(c_579, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_572, c_34])).
% 3.40/1.65  tff(c_586, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_579])).
% 3.40/1.65  tff(c_588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_586])).
% 3.40/1.65  tff(c_589, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_60])).
% 3.40/1.65  tff(c_922, plain, (![B_175, A_176]: (r1_xboole_0(k1_relat_1(B_175), A_176) | k7_relat_1(B_175, A_176)!=k1_xboole_0 | ~v1_relat_1(B_175))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.40/1.65  tff(c_8, plain, (![B_7, A_6]: (r1_xboole_0(B_7, A_6) | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.40/1.65  tff(c_1018, plain, (![A_184, B_185]: (r1_xboole_0(A_184, k1_relat_1(B_185)) | k7_relat_1(B_185, A_184)!=k1_xboole_0 | ~v1_relat_1(B_185))), inference(resolution, [status(thm)], [c_922, c_8])).
% 3.40/1.65  tff(c_14, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.40/1.65  tff(c_644, plain, (![A_137, C_138, B_139]: (~r2_hidden(A_137, C_138) | ~r1_xboole_0(k2_tarski(A_137, B_139), C_138))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.40/1.65  tff(c_651, plain, (![A_11, C_138]: (~r2_hidden(A_11, C_138) | ~r1_xboole_0(k1_tarski(A_11), C_138))), inference(superposition, [status(thm), theory('equality')], [c_14, c_644])).
% 3.40/1.65  tff(c_1118, plain, (![A_202, B_203]: (~r2_hidden(A_202, k1_relat_1(B_203)) | k7_relat_1(B_203, k1_tarski(A_202))!=k1_xboole_0 | ~v1_relat_1(B_203))), inference(resolution, [status(thm)], [c_1018, c_651])).
% 3.40/1.65  tff(c_1140, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_3'))!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_589, c_1118])).
% 3.40/1.65  tff(c_1151, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1140])).
% 3.40/1.65  tff(c_36, plain, (![A_36, B_37]: (v1_relat_1(k7_relat_1(A_36, B_37)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.40/1.65  tff(c_28, plain, (![A_28]: (k2_zfmisc_1(A_28, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.40/1.65  tff(c_590, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 3.40/1.65  tff(c_735, plain, (![B_154, A_155]: (k2_relat_1(k7_relat_1(B_154, A_155))=k9_relat_1(B_154, A_155) | ~v1_relat_1(B_154))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.40/1.65  tff(c_42, plain, (![A_43]: (r1_tarski(A_43, k2_zfmisc_1(k1_relat_1(A_43), k2_relat_1(A_43))) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.40/1.65  tff(c_1322, plain, (![B_230, A_231]: (r1_tarski(k7_relat_1(B_230, A_231), k2_zfmisc_1(k1_relat_1(k7_relat_1(B_230, A_231)), k9_relat_1(B_230, A_231))) | ~v1_relat_1(k7_relat_1(B_230, A_231)) | ~v1_relat_1(B_230))), inference(superposition, [status(thm), theory('equality')], [c_735, c_42])).
% 3.40/1.65  tff(c_1634, plain, (![A_281, B_282]: (r1_tarski(k7_relat_1(A_281, k1_tarski(B_282)), k2_zfmisc_1(k1_relat_1(k7_relat_1(A_281, k1_tarski(B_282))), k11_relat_1(A_281, B_282))) | ~v1_relat_1(k7_relat_1(A_281, k1_tarski(B_282))) | ~v1_relat_1(A_281) | ~v1_relat_1(A_281))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1322])).
% 3.40/1.65  tff(c_1658, plain, (r1_tarski(k7_relat_1('#skF_4', k1_tarski('#skF_3')), k2_zfmisc_1(k1_relat_1(k7_relat_1('#skF_4', k1_tarski('#skF_3'))), k1_xboole_0)) | ~v1_relat_1(k7_relat_1('#skF_4', k1_tarski('#skF_3'))) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_590, c_1634])).
% 3.40/1.65  tff(c_1670, plain, (r1_tarski(k7_relat_1('#skF_4', k1_tarski('#skF_3')), k1_xboole_0) | ~v1_relat_1(k7_relat_1('#skF_4', k1_tarski('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_28, c_1658])).
% 3.40/1.65  tff(c_1714, plain, (~v1_relat_1(k7_relat_1('#skF_4', k1_tarski('#skF_3')))), inference(splitLeft, [status(thm)], [c_1670])).
% 3.40/1.65  tff(c_1717, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1714])).
% 3.40/1.65  tff(c_1721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1717])).
% 3.40/1.65  tff(c_1722, plain, (r1_tarski(k7_relat_1('#skF_4', k1_tarski('#skF_3')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1670])).
% 3.40/1.65  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.40/1.65  tff(c_671, plain, (![C_142, B_143, A_144]: (r2_hidden(C_142, B_143) | ~r2_hidden(C_142, A_144) | ~r1_tarski(A_144, B_143))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.40/1.65  tff(c_756, plain, (![A_158, B_159]: (r2_hidden('#skF_2'(A_158), B_159) | ~r1_tarski(A_158, B_159) | k1_xboole_0=A_158)), inference(resolution, [status(thm)], [c_10, c_671])).
% 3.40/1.65  tff(c_12, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.40/1.65  tff(c_657, plain, (![A_137]: (~r2_hidden(A_137, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_644])).
% 3.40/1.65  tff(c_768, plain, (![A_158]: (~r1_tarski(A_158, k1_xboole_0) | k1_xboole_0=A_158)), inference(resolution, [status(thm)], [c_756, c_657])).
% 3.40/1.65  tff(c_1736, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1722, c_768])).
% 3.40/1.65  tff(c_1747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1151, c_1736])).
% 3.40/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.65  
% 3.40/1.65  Inference rules
% 3.40/1.65  ----------------------
% 3.40/1.65  #Ref     : 0
% 3.40/1.65  #Sup     : 375
% 3.40/1.65  #Fact    : 0
% 3.40/1.65  #Define  : 0
% 3.40/1.65  #Split   : 6
% 3.40/1.65  #Chain   : 0
% 3.40/1.65  #Close   : 0
% 3.40/1.65  
% 3.40/1.65  Ordering : KBO
% 3.40/1.65  
% 3.40/1.65  Simplification rules
% 3.40/1.65  ----------------------
% 3.40/1.65  #Subsume      : 48
% 3.40/1.65  #Demod        : 225
% 3.40/1.65  #Tautology    : 166
% 3.40/1.65  #SimpNegUnit  : 9
% 3.40/1.65  #BackRed      : 0
% 3.40/1.65  
% 3.40/1.65  #Partial instantiations: 0
% 3.40/1.65  #Strategies tried      : 1
% 3.40/1.65  
% 3.40/1.65  Timing (in seconds)
% 3.40/1.65  ----------------------
% 3.40/1.65  Preprocessing        : 0.33
% 3.40/1.65  Parsing              : 0.18
% 3.40/1.65  CNF conversion       : 0.02
% 3.40/1.65  Main loop            : 0.50
% 3.40/1.65  Inferencing          : 0.19
% 3.40/1.65  Reduction            : 0.15
% 3.40/1.65  Demodulation         : 0.10
% 3.40/1.65  BG Simplification    : 0.02
% 3.40/1.65  Subsumption          : 0.10
% 3.40/1.65  Abstraction          : 0.02
% 3.40/1.65  MUC search           : 0.00
% 3.40/1.65  Cooper               : 0.00
% 3.40/1.65  Total                : 0.87
% 3.40/1.65  Index Insertion      : 0.00
% 3.40/1.65  Index Deletion       : 0.00
% 3.40/1.65  Index Matching       : 0.00
% 3.40/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
