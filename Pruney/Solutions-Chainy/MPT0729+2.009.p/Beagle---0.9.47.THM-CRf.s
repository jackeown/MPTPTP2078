%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:59 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 242 expanded)
%              Number of leaves         :   31 (  92 expanded)
%              Depth                    :   10
%              Number of atoms          :  116 ( 391 expanded)
%              Number of equality atoms :   27 ( 105 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_79,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( k1_ordinal1(A) = k1_ordinal1(B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).

tff(f_81,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_34,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(k1_tarski(A_36),B_37)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,(
    ! [A_42] : k2_xboole_0(A_42,k1_tarski(A_42)) = k1_ordinal1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_322,plain,(
    ! [A_102,C_103,B_104] :
      ( r1_tarski(k2_xboole_0(A_102,C_103),B_104)
      | ~ r1_tarski(C_103,B_104)
      | ~ r1_tarski(A_102,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_737,plain,(
    ! [A_138,B_139] :
      ( r1_tarski(k1_ordinal1(A_138),B_139)
      | ~ r1_tarski(k1_tarski(A_138),B_139)
      | ~ r1_tarski(A_138,B_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_322])).

tff(c_792,plain,(
    ! [A_144,B_145] :
      ( r1_tarski(k1_ordinal1(A_144),B_145)
      | ~ r1_tarski(A_144,B_145)
      | ~ r2_hidden(A_144,B_145) ) ),
    inference(resolution,[status(thm)],[c_34,c_737])).

tff(c_50,plain,(
    k1_ordinal1('#skF_2') = k1_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_44,plain,(
    ! [A_43] : r2_hidden(A_43,k1_ordinal1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_57,plain,(
    r2_hidden('#skF_2',k1_ordinal1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_44])).

tff(c_98,plain,(
    ! [B_56,A_57] :
      ( ~ r1_tarski(B_56,A_57)
      | ~ r2_hidden(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_105,plain,(
    ~ r1_tarski(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_57,c_98])).

tff(c_830,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_792,c_105])).

tff(c_834,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_830])).

tff(c_40,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,k1_tarski(B_41)) = A_40
      | r2_hidden(B_41,A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_835,plain,(
    ! [B_146] :
      ( r1_tarski(k1_ordinal1('#skF_1'),B_146)
      | ~ r1_tarski('#skF_2',B_146)
      | ~ r2_hidden('#skF_2',B_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_792])).

tff(c_106,plain,(
    ! [A_43] : ~ r1_tarski(k1_ordinal1(A_43),A_43) ),
    inference(resolution,[status(thm)],[c_44,c_98])).

tff(c_868,plain,
    ( ~ r1_tarski('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_835,c_106])).

tff(c_869,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_868])).

tff(c_48,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_82,plain,(
    ! [A_54] : k2_xboole_0(A_54,k1_tarski(A_54)) = k1_ordinal1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_94,plain,(
    ! [A_55] : r1_tarski(A_55,k1_ordinal1(A_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_12])).

tff(c_97,plain,(
    r1_tarski('#skF_2',k1_ordinal1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_94])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_466,plain,(
    ! [A_110,B_111,C_112] :
      ( r1_tarski(A_110,B_111)
      | ~ r1_xboole_0(A_110,C_112)
      | ~ r1_tarski(A_110,k2_xboole_0(B_111,C_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_786,plain,(
    ! [A_142,A_143] :
      ( r1_tarski(A_142,A_143)
      | ~ r1_xboole_0(A_142,k1_tarski(A_143))
      | ~ r1_tarski(A_142,k1_ordinal1(A_143)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_466])).

tff(c_1149,plain,(
    ! [A_156,A_157] :
      ( r1_tarski(A_156,A_157)
      | ~ r1_tarski(A_156,k1_ordinal1(A_157))
      | k4_xboole_0(A_156,k1_tarski(A_157)) != A_156 ) ),
    inference(resolution,[status(thm)],[c_16,c_786])).

tff(c_1187,plain,
    ( r1_tarski('#skF_2','#skF_1')
    | k4_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_97,c_1149])).

tff(c_1192,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1187])).

tff(c_1195,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1192])).

tff(c_1199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_834,c_1195])).

tff(c_1200,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1187])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1273,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_1200,c_4])).

tff(c_1277,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1273])).

tff(c_88,plain,(
    ! [A_54] : r1_tarski(A_54,k1_ordinal1(A_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_12])).

tff(c_1311,plain,(
    ! [A_161] :
      ( r1_tarski(A_161,'#skF_2')
      | ~ r1_tarski(A_161,k1_ordinal1('#skF_1'))
      | k4_xboole_0(A_161,k1_tarski('#skF_2')) != A_161 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1149])).

tff(c_1334,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_88,c_1311])).

tff(c_1350,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_1277,c_1334])).

tff(c_1373,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1350])).

tff(c_1377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_869,c_1373])).

tff(c_1378,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_868])).

tff(c_1740,plain,(
    ! [A_176,A_177] :
      ( r1_tarski(A_176,A_177)
      | ~ r1_tarski(A_176,k1_ordinal1(A_177))
      | k4_xboole_0(A_176,k1_tarski(A_177)) != A_176 ) ),
    inference(resolution,[status(thm)],[c_16,c_786])).

tff(c_1762,plain,
    ( r1_tarski('#skF_2','#skF_1')
    | k4_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_97,c_1740])).

tff(c_1780,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1378,c_1762])).

tff(c_1787,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1780])).

tff(c_1791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_834,c_1787])).

tff(c_1793,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_830])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1834,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_1793,c_2])).

tff(c_1792,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_830])).

tff(c_2188,plain,(
    ! [A_193,A_194] :
      ( r1_tarski(A_193,A_194)
      | ~ r1_tarski(A_193,k1_ordinal1(A_194))
      | k4_xboole_0(A_193,k1_tarski(A_194)) != A_193 ) ),
    inference(resolution,[status(thm)],[c_16,c_786])).

tff(c_2238,plain,(
    ! [A_195] :
      ( r1_tarski(A_195,'#skF_2')
      | ~ r1_tarski(A_195,k1_ordinal1('#skF_1'))
      | k4_xboole_0(A_195,k1_tarski('#skF_2')) != A_195 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2188])).

tff(c_2261,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_88,c_2238])).

tff(c_2277,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_1792,c_2261])).

tff(c_2282,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2277])).

tff(c_2286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1834,c_2282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:29:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.97  
% 4.03/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.98  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 4.03/1.98  
% 4.03/1.98  %Foreground sorts:
% 4.03/1.98  
% 4.03/1.98  
% 4.03/1.98  %Background operators:
% 4.03/1.98  
% 4.03/1.98  
% 4.03/1.98  %Foreground operators:
% 4.03/1.98  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 4.03/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.03/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.03/1.98  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.03/1.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.03/1.98  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.03/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.03/1.98  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.03/1.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.03/1.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.03/1.98  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.03/1.98  tff('#skF_2', type, '#skF_2': $i).
% 4.03/1.98  tff('#skF_1', type, '#skF_1': $i).
% 4.03/1.98  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.03/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.03/1.98  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.03/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.03/1.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.03/1.98  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.03/1.98  
% 4.03/1.99  tff(f_70, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.03/1.99  tff(f_79, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 4.03/1.99  tff(f_54, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 4.03/1.99  tff(f_91, negated_conjecture, ~(![A, B]: ((k1_ordinal1(A) = k1_ordinal1(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_ordinal1)).
% 4.03/1.99  tff(f_81, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 4.03/1.99  tff(f_86, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.03/1.99  tff(f_77, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.03/1.99  tff(f_44, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.03/1.99  tff(f_48, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.03/1.99  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 4.03/1.99  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.03/1.99  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 4.03/1.99  tff(c_34, plain, (![A_36, B_37]: (r1_tarski(k1_tarski(A_36), B_37) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.03/1.99  tff(c_42, plain, (![A_42]: (k2_xboole_0(A_42, k1_tarski(A_42))=k1_ordinal1(A_42))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.03/1.99  tff(c_322, plain, (![A_102, C_103, B_104]: (r1_tarski(k2_xboole_0(A_102, C_103), B_104) | ~r1_tarski(C_103, B_104) | ~r1_tarski(A_102, B_104))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.03/1.99  tff(c_737, plain, (![A_138, B_139]: (r1_tarski(k1_ordinal1(A_138), B_139) | ~r1_tarski(k1_tarski(A_138), B_139) | ~r1_tarski(A_138, B_139))), inference(superposition, [status(thm), theory('equality')], [c_42, c_322])).
% 4.03/1.99  tff(c_792, plain, (![A_144, B_145]: (r1_tarski(k1_ordinal1(A_144), B_145) | ~r1_tarski(A_144, B_145) | ~r2_hidden(A_144, B_145))), inference(resolution, [status(thm)], [c_34, c_737])).
% 4.03/1.99  tff(c_50, plain, (k1_ordinal1('#skF_2')=k1_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.03/1.99  tff(c_44, plain, (![A_43]: (r2_hidden(A_43, k1_ordinal1(A_43)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.03/1.99  tff(c_57, plain, (r2_hidden('#skF_2', k1_ordinal1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_44])).
% 4.03/1.99  tff(c_98, plain, (![B_56, A_57]: (~r1_tarski(B_56, A_57) | ~r2_hidden(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.03/1.99  tff(c_105, plain, (~r1_tarski(k1_ordinal1('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_57, c_98])).
% 4.03/1.99  tff(c_830, plain, (~r1_tarski('#skF_1', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_792, c_105])).
% 4.03/1.99  tff(c_834, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_830])).
% 4.03/1.99  tff(c_40, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k1_tarski(B_41))=A_40 | r2_hidden(B_41, A_40))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.03/1.99  tff(c_835, plain, (![B_146]: (r1_tarski(k1_ordinal1('#skF_1'), B_146) | ~r1_tarski('#skF_2', B_146) | ~r2_hidden('#skF_2', B_146))), inference(superposition, [status(thm), theory('equality')], [c_50, c_792])).
% 4.03/1.99  tff(c_106, plain, (![A_43]: (~r1_tarski(k1_ordinal1(A_43), A_43))), inference(resolution, [status(thm)], [c_44, c_98])).
% 4.03/1.99  tff(c_868, plain, (~r1_tarski('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_835, c_106])).
% 4.03/1.99  tff(c_869, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_868])).
% 4.03/1.99  tff(c_48, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.03/1.99  tff(c_82, plain, (![A_54]: (k2_xboole_0(A_54, k1_tarski(A_54))=k1_ordinal1(A_54))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.03/1.99  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.03/1.99  tff(c_94, plain, (![A_55]: (r1_tarski(A_55, k1_ordinal1(A_55)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_12])).
% 4.03/1.99  tff(c_97, plain, (r1_tarski('#skF_2', k1_ordinal1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_94])).
% 4.03/1.99  tff(c_16, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.03/1.99  tff(c_466, plain, (![A_110, B_111, C_112]: (r1_tarski(A_110, B_111) | ~r1_xboole_0(A_110, C_112) | ~r1_tarski(A_110, k2_xboole_0(B_111, C_112)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.03/1.99  tff(c_786, plain, (![A_142, A_143]: (r1_tarski(A_142, A_143) | ~r1_xboole_0(A_142, k1_tarski(A_143)) | ~r1_tarski(A_142, k1_ordinal1(A_143)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_466])).
% 4.03/1.99  tff(c_1149, plain, (![A_156, A_157]: (r1_tarski(A_156, A_157) | ~r1_tarski(A_156, k1_ordinal1(A_157)) | k4_xboole_0(A_156, k1_tarski(A_157))!=A_156)), inference(resolution, [status(thm)], [c_16, c_786])).
% 4.03/1.99  tff(c_1187, plain, (r1_tarski('#skF_2', '#skF_1') | k4_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(resolution, [status(thm)], [c_97, c_1149])).
% 4.03/1.99  tff(c_1192, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_1187])).
% 4.03/1.99  tff(c_1195, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_40, c_1192])).
% 4.03/1.99  tff(c_1199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_834, c_1195])).
% 4.03/1.99  tff(c_1200, plain, (r1_tarski('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_1187])).
% 4.03/1.99  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.03/1.99  tff(c_1273, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_1200, c_4])).
% 4.03/1.99  tff(c_1277, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_1273])).
% 4.03/1.99  tff(c_88, plain, (![A_54]: (r1_tarski(A_54, k1_ordinal1(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_12])).
% 4.03/1.99  tff(c_1311, plain, (![A_161]: (r1_tarski(A_161, '#skF_2') | ~r1_tarski(A_161, k1_ordinal1('#skF_1')) | k4_xboole_0(A_161, k1_tarski('#skF_2'))!=A_161)), inference(superposition, [status(thm), theory('equality')], [c_50, c_1149])).
% 4.03/1.99  tff(c_1334, plain, (r1_tarski('#skF_1', '#skF_2') | k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(resolution, [status(thm)], [c_88, c_1311])).
% 4.03/1.99  tff(c_1350, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_1277, c_1334])).
% 4.03/1.99  tff(c_1373, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40, c_1350])).
% 4.03/1.99  tff(c_1377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_869, c_1373])).
% 4.03/1.99  tff(c_1378, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_868])).
% 4.03/1.99  tff(c_1740, plain, (![A_176, A_177]: (r1_tarski(A_176, A_177) | ~r1_tarski(A_176, k1_ordinal1(A_177)) | k4_xboole_0(A_176, k1_tarski(A_177))!=A_176)), inference(resolution, [status(thm)], [c_16, c_786])).
% 4.03/1.99  tff(c_1762, plain, (r1_tarski('#skF_2', '#skF_1') | k4_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(resolution, [status(thm)], [c_97, c_1740])).
% 4.03/1.99  tff(c_1780, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1378, c_1762])).
% 4.03/1.99  tff(c_1787, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_40, c_1780])).
% 4.03/1.99  tff(c_1791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_834, c_1787])).
% 4.03/1.99  tff(c_1793, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_830])).
% 4.03/1.99  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.03/1.99  tff(c_1834, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_1793, c_2])).
% 4.03/1.99  tff(c_1792, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_830])).
% 4.03/1.99  tff(c_2188, plain, (![A_193, A_194]: (r1_tarski(A_193, A_194) | ~r1_tarski(A_193, k1_ordinal1(A_194)) | k4_xboole_0(A_193, k1_tarski(A_194))!=A_193)), inference(resolution, [status(thm)], [c_16, c_786])).
% 4.03/1.99  tff(c_2238, plain, (![A_195]: (r1_tarski(A_195, '#skF_2') | ~r1_tarski(A_195, k1_ordinal1('#skF_1')) | k4_xboole_0(A_195, k1_tarski('#skF_2'))!=A_195)), inference(superposition, [status(thm), theory('equality')], [c_50, c_2188])).
% 4.03/1.99  tff(c_2261, plain, (r1_tarski('#skF_1', '#skF_2') | k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(resolution, [status(thm)], [c_88, c_2238])).
% 4.03/1.99  tff(c_2277, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_1792, c_2261])).
% 4.03/1.99  tff(c_2282, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40, c_2277])).
% 4.03/1.99  tff(c_2286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1834, c_2282])).
% 4.03/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.99  
% 4.03/1.99  Inference rules
% 4.03/1.99  ----------------------
% 4.03/1.99  #Ref     : 0
% 4.03/1.99  #Sup     : 501
% 4.03/1.99  #Fact    : 0
% 4.03/1.99  #Define  : 0
% 4.03/1.99  #Split   : 7
% 4.03/1.99  #Chain   : 0
% 4.03/1.99  #Close   : 0
% 4.03/1.99  
% 4.03/1.99  Ordering : KBO
% 4.03/1.99  
% 4.03/1.99  Simplification rules
% 4.03/1.99  ----------------------
% 4.03/1.99  #Subsume      : 119
% 4.03/1.99  #Demod        : 191
% 4.03/1.99  #Tautology    : 229
% 4.03/1.99  #SimpNegUnit  : 19
% 4.03/1.99  #BackRed      : 5
% 4.03/1.99  
% 4.03/1.99  #Partial instantiations: 0
% 4.03/1.99  #Strategies tried      : 1
% 4.03/1.99  
% 4.03/1.99  Timing (in seconds)
% 4.03/1.99  ----------------------
% 4.03/1.99  Preprocessing        : 0.46
% 4.03/1.99  Parsing              : 0.29
% 4.03/1.99  CNF conversion       : 0.02
% 4.03/1.99  Main loop            : 0.59
% 4.03/2.00  Inferencing          : 0.21
% 4.03/2.00  Reduction            : 0.19
% 4.03/2.00  Demodulation         : 0.13
% 4.03/2.00  BG Simplification    : 0.03
% 4.03/2.00  Subsumption          : 0.13
% 4.03/2.00  Abstraction          : 0.03
% 4.03/2.00  MUC search           : 0.00
% 4.03/2.00  Cooper               : 0.00
% 4.03/2.00  Total                : 1.08
% 4.03/2.00  Index Insertion      : 0.00
% 4.03/2.00  Index Deletion       : 0.00
% 4.03/2.00  Index Matching       : 0.00
% 4.03/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
