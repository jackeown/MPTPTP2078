%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:01 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 185 expanded)
%              Number of leaves         :   36 (  77 expanded)
%              Depth                    :   16
%              Number of atoms          :  133 ( 336 expanded)
%              Number of equality atoms :   41 (  73 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_116,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_113,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_105,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_120,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_76,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_72,plain,(
    ! [A_42] : ~ v1_xboole_0(k1_zfmisc_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_187,plain,(
    ! [B_70,A_71] :
      ( r2_hidden(B_70,A_71)
      | ~ m1_subset_1(B_70,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    ! [C_34,A_30] :
      ( r1_tarski(C_34,A_30)
      | ~ r2_hidden(C_34,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_191,plain,(
    ! [B_70,A_30] :
      ( r1_tarski(B_70,A_30)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_30))
      | v1_xboole_0(k1_zfmisc_1(A_30)) ) ),
    inference(resolution,[status(thm)],[c_187,c_46])).

tff(c_195,plain,(
    ! [B_72,A_73] :
      ( r1_tarski(B_72,A_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_191])).

tff(c_204,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_76,c_195])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_293,plain,(
    ! [A_82,B_83] :
      ( ~ r2_hidden('#skF_1'(A_82,B_83),B_83)
      | r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_313,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_293])).

tff(c_48,plain,(
    ! [C_34,A_30] :
      ( r2_hidden(C_34,k1_zfmisc_1(A_30))
      | ~ r1_tarski(C_34,A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_444,plain,(
    ! [B_94,A_95] :
      ( m1_subset_1(B_94,A_95)
      | ~ r2_hidden(B_94,A_95)
      | v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_462,plain,(
    ! [C_34,A_30] :
      ( m1_subset_1(C_34,k1_zfmisc_1(A_30))
      | v1_xboole_0(k1_zfmisc_1(A_30))
      | ~ r1_tarski(C_34,A_30) ) ),
    inference(resolution,[status(thm)],[c_48,c_444])).

tff(c_473,plain,(
    ! [C_34,A_30] :
      ( m1_subset_1(C_34,k1_zfmisc_1(A_30))
      | ~ r1_tarski(C_34,A_30) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_462])).

tff(c_1323,plain,(
    ! [A_152,B_153] :
      ( m1_subset_1(k3_subset_1(A_152,B_153),k1_zfmisc_1(A_152))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(A_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_194,plain,(
    ! [B_70,A_30] :
      ( r1_tarski(B_70,A_30)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_30)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_191])).

tff(c_1343,plain,(
    ! [A_152,B_153] :
      ( r1_tarski(k3_subset_1(A_152,B_153),A_152)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(A_152)) ) ),
    inference(resolution,[status(thm)],[c_1323,c_194])).

tff(c_1230,plain,(
    ! [A_146,B_147] :
      ( k4_xboole_0(A_146,B_147) = k3_subset_1(A_146,B_147)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(A_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1481,plain,(
    ! [A_160,C_161] :
      ( k4_xboole_0(A_160,C_161) = k3_subset_1(A_160,C_161)
      | ~ r1_tarski(C_161,A_160) ) ),
    inference(resolution,[status(thm)],[c_473,c_1230])).

tff(c_1496,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k3_subset_1(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_313,c_1481])).

tff(c_1545,plain,(
    ! [A_165] : k4_xboole_0(A_165,A_165) = k3_subset_1(A_165,A_165) ),
    inference(resolution,[status(thm)],[c_313,c_1481])).

tff(c_315,plain,(
    ! [A_84] : r1_tarski(A_84,A_84) ),
    inference(resolution,[status(thm)],[c_8,c_293])).

tff(c_42,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_319,plain,(
    ! [A_84] : k3_xboole_0(A_84,A_84) = A_84 ),
    inference(resolution,[status(thm)],[c_315,c_42])).

tff(c_288,plain,(
    ! [A_79,C_80,B_81] :
      ( r1_xboole_0(A_79,k4_xboole_0(C_80,B_81))
      | ~ r1_tarski(A_79,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_66,plain,(
    ! [A_37] : k1_subset_1(A_37) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_78,plain,
    ( k1_subset_1('#skF_8') != '#skF_9'
    | ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_86,plain,
    ( k1_xboole_0 != '#skF_9'
    | ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_78])).

tff(c_129,plain,(
    ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_84,plain,
    ( r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9'))
    | k1_subset_1('#skF_8') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_85,plain,
    ( r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_84])).

tff(c_130,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_85])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_163,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = '#skF_9'
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_28])).

tff(c_595,plain,(
    ! [A_111,C_112,B_113] :
      ( k3_xboole_0(A_111,k4_xboole_0(C_112,B_113)) = '#skF_9'
      | ~ r1_tarski(A_111,B_113) ) ),
    inference(resolution,[status(thm)],[c_288,c_163])).

tff(c_630,plain,(
    ! [C_112,B_113] :
      ( k4_xboole_0(C_112,B_113) = '#skF_9'
      | ~ r1_tarski(k4_xboole_0(C_112,B_113),B_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_595])).

tff(c_1554,plain,(
    ! [A_165] :
      ( k4_xboole_0(A_165,A_165) = '#skF_9'
      | ~ r1_tarski(k3_subset_1(A_165,A_165),A_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1545,c_630])).

tff(c_1786,plain,(
    ! [A_174] :
      ( k3_subset_1(A_174,A_174) = '#skF_9'
      | ~ r1_tarski(k3_subset_1(A_174,A_174),A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1496,c_1554])).

tff(c_1797,plain,(
    ! [B_175] :
      ( k3_subset_1(B_175,B_175) = '#skF_9'
      | ~ m1_subset_1(B_175,k1_zfmisc_1(B_175)) ) ),
    inference(resolution,[status(thm)],[c_1343,c_1786])).

tff(c_1801,plain,(
    ! [A_30] :
      ( k3_subset_1(A_30,A_30) = '#skF_9'
      | ~ r1_tarski(A_30,A_30) ) ),
    inference(resolution,[status(thm)],[c_473,c_1797])).

tff(c_1866,plain,(
    ! [A_178] : k3_subset_1(A_178,A_178) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_1801])).

tff(c_814,plain,(
    ! [A_123,B_124] :
      ( k3_subset_1(A_123,k3_subset_1(A_123,B_124)) = B_124
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_828,plain,(
    ! [A_30,C_34] :
      ( k3_subset_1(A_30,k3_subset_1(A_30,C_34)) = C_34
      | ~ r1_tarski(C_34,A_30) ) ),
    inference(resolution,[status(thm)],[c_473,c_814])).

tff(c_1877,plain,(
    ! [A_178] :
      ( k3_subset_1(A_178,'#skF_9') = A_178
      | ~ r1_tarski(A_178,A_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1866,c_828])).

tff(c_1882,plain,(
    ! [A_178] : k3_subset_1(A_178,'#skF_9') = A_178 ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_1877])).

tff(c_1920,plain,(
    ~ r1_tarski('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1882,c_129])).

tff(c_1924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_1920])).

tff(c_1925,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_1995,plain,(
    ! [A_201,B_202] :
      ( ~ r2_hidden('#skF_1'(A_201,B_202),B_202)
      | r1_tarski(A_201,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2004,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_1995])).

tff(c_2879,plain,(
    ! [A_267,B_268] :
      ( k4_xboole_0(A_267,B_268) = k3_subset_1(A_267,B_268)
      | ~ m1_subset_1(B_268,k1_zfmisc_1(A_267)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2903,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_2879])).

tff(c_2261,plain,(
    ! [A_223,C_224,B_225] :
      ( r1_xboole_0(A_223,k4_xboole_0(C_224,B_225))
      | ~ r1_tarski(A_223,B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2268,plain,(
    ! [A_223,C_224,B_225] :
      ( k3_xboole_0(A_223,k4_xboole_0(C_224,B_225)) = k1_xboole_0
      | ~ r1_tarski(A_223,B_225) ) ),
    inference(resolution,[status(thm)],[c_2261,c_28])).

tff(c_2934,plain,(
    ! [A_270] :
      ( k3_xboole_0(A_270,k3_subset_1('#skF_8','#skF_9')) = k1_xboole_0
      | ~ r1_tarski(A_270,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2903,c_2268])).

tff(c_1926,plain,(
    r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_1956,plain,(
    ! [A_193,B_194] :
      ( k3_xboole_0(A_193,B_194) = A_193
      | ~ r1_tarski(A_193,B_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1960,plain,(
    k3_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1926,c_1956])).

tff(c_2964,plain,
    ( k1_xboole_0 = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_2934,c_1960])).

tff(c_3000,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2004,c_2964])).

tff(c_3002,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1925,c_3000])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:24:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.76  
% 3.98/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.76  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_4
% 3.98/1.76  
% 3.98/1.76  %Foreground sorts:
% 3.98/1.76  
% 3.98/1.76  
% 3.98/1.76  %Background operators:
% 3.98/1.76  
% 3.98/1.76  
% 3.98/1.76  %Foreground operators:
% 3.98/1.76  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.98/1.76  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.98/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.98/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.98/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.98/1.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.98/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.98/1.76  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.98/1.76  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.98/1.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.98/1.76  tff('#skF_9', type, '#skF_9': $i).
% 3.98/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.98/1.76  tff('#skF_8', type, '#skF_8': $i).
% 3.98/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.76  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.98/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.76  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.98/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.98/1.76  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.98/1.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.98/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.98/1.76  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.98/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.98/1.76  
% 4.40/1.78  tff(f_127, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 4.40/1.78  tff(f_116, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.40/1.78  tff(f_103, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.40/1.78  tff(f_90, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.40/1.78  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.40/1.78  tff(f_113, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.40/1.78  tff(f_109, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.40/1.78  tff(f_79, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.40/1.78  tff(f_83, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 4.40/1.78  tff(f_105, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 4.40/1.78  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.40/1.78  tff(f_120, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.40/1.78  tff(c_76, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.40/1.78  tff(c_72, plain, (![A_42]: (~v1_xboole_0(k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.40/1.78  tff(c_187, plain, (![B_70, A_71]: (r2_hidden(B_70, A_71) | ~m1_subset_1(B_70, A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.40/1.78  tff(c_46, plain, (![C_34, A_30]: (r1_tarski(C_34, A_30) | ~r2_hidden(C_34, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.40/1.78  tff(c_191, plain, (![B_70, A_30]: (r1_tarski(B_70, A_30) | ~m1_subset_1(B_70, k1_zfmisc_1(A_30)) | v1_xboole_0(k1_zfmisc_1(A_30)))), inference(resolution, [status(thm)], [c_187, c_46])).
% 4.40/1.78  tff(c_195, plain, (![B_72, A_73]: (r1_tarski(B_72, A_73) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)))), inference(negUnitSimplification, [status(thm)], [c_72, c_191])).
% 4.40/1.78  tff(c_204, plain, (r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_76, c_195])).
% 4.40/1.78  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.40/1.78  tff(c_293, plain, (![A_82, B_83]: (~r2_hidden('#skF_1'(A_82, B_83), B_83) | r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.40/1.78  tff(c_313, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_293])).
% 4.40/1.78  tff(c_48, plain, (![C_34, A_30]: (r2_hidden(C_34, k1_zfmisc_1(A_30)) | ~r1_tarski(C_34, A_30))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.40/1.78  tff(c_444, plain, (![B_94, A_95]: (m1_subset_1(B_94, A_95) | ~r2_hidden(B_94, A_95) | v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.40/1.78  tff(c_462, plain, (![C_34, A_30]: (m1_subset_1(C_34, k1_zfmisc_1(A_30)) | v1_xboole_0(k1_zfmisc_1(A_30)) | ~r1_tarski(C_34, A_30))), inference(resolution, [status(thm)], [c_48, c_444])).
% 4.40/1.78  tff(c_473, plain, (![C_34, A_30]: (m1_subset_1(C_34, k1_zfmisc_1(A_30)) | ~r1_tarski(C_34, A_30))), inference(negUnitSimplification, [status(thm)], [c_72, c_462])).
% 4.40/1.78  tff(c_1323, plain, (![A_152, B_153]: (m1_subset_1(k3_subset_1(A_152, B_153), k1_zfmisc_1(A_152)) | ~m1_subset_1(B_153, k1_zfmisc_1(A_152)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.40/1.78  tff(c_194, plain, (![B_70, A_30]: (r1_tarski(B_70, A_30) | ~m1_subset_1(B_70, k1_zfmisc_1(A_30)))), inference(negUnitSimplification, [status(thm)], [c_72, c_191])).
% 4.40/1.78  tff(c_1343, plain, (![A_152, B_153]: (r1_tarski(k3_subset_1(A_152, B_153), A_152) | ~m1_subset_1(B_153, k1_zfmisc_1(A_152)))), inference(resolution, [status(thm)], [c_1323, c_194])).
% 4.40/1.78  tff(c_1230, plain, (![A_146, B_147]: (k4_xboole_0(A_146, B_147)=k3_subset_1(A_146, B_147) | ~m1_subset_1(B_147, k1_zfmisc_1(A_146)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.40/1.78  tff(c_1481, plain, (![A_160, C_161]: (k4_xboole_0(A_160, C_161)=k3_subset_1(A_160, C_161) | ~r1_tarski(C_161, A_160))), inference(resolution, [status(thm)], [c_473, c_1230])).
% 4.40/1.78  tff(c_1496, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k3_subset_1(A_3, A_3))), inference(resolution, [status(thm)], [c_313, c_1481])).
% 4.40/1.78  tff(c_1545, plain, (![A_165]: (k4_xboole_0(A_165, A_165)=k3_subset_1(A_165, A_165))), inference(resolution, [status(thm)], [c_313, c_1481])).
% 4.40/1.78  tff(c_315, plain, (![A_84]: (r1_tarski(A_84, A_84))), inference(resolution, [status(thm)], [c_8, c_293])).
% 4.40/1.78  tff(c_42, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.40/1.78  tff(c_319, plain, (![A_84]: (k3_xboole_0(A_84, A_84)=A_84)), inference(resolution, [status(thm)], [c_315, c_42])).
% 4.40/1.78  tff(c_288, plain, (![A_79, C_80, B_81]: (r1_xboole_0(A_79, k4_xboole_0(C_80, B_81)) | ~r1_tarski(A_79, B_81))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.40/1.78  tff(c_66, plain, (![A_37]: (k1_subset_1(A_37)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.40/1.78  tff(c_78, plain, (k1_subset_1('#skF_8')!='#skF_9' | ~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.40/1.78  tff(c_86, plain, (k1_xboole_0!='#skF_9' | ~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_78])).
% 4.40/1.78  tff(c_129, plain, (~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_86])).
% 4.40/1.78  tff(c_84, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9')) | k1_subset_1('#skF_8')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.40/1.78  tff(c_85, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9')) | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_84])).
% 4.40/1.78  tff(c_130, plain, (k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_129, c_85])).
% 4.40/1.78  tff(c_28, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.40/1.78  tff(c_163, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)='#skF_9' | ~r1_xboole_0(A_14, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_28])).
% 4.40/1.78  tff(c_595, plain, (![A_111, C_112, B_113]: (k3_xboole_0(A_111, k4_xboole_0(C_112, B_113))='#skF_9' | ~r1_tarski(A_111, B_113))), inference(resolution, [status(thm)], [c_288, c_163])).
% 4.40/1.78  tff(c_630, plain, (![C_112, B_113]: (k4_xboole_0(C_112, B_113)='#skF_9' | ~r1_tarski(k4_xboole_0(C_112, B_113), B_113))), inference(superposition, [status(thm), theory('equality')], [c_319, c_595])).
% 4.40/1.78  tff(c_1554, plain, (![A_165]: (k4_xboole_0(A_165, A_165)='#skF_9' | ~r1_tarski(k3_subset_1(A_165, A_165), A_165))), inference(superposition, [status(thm), theory('equality')], [c_1545, c_630])).
% 4.40/1.78  tff(c_1786, plain, (![A_174]: (k3_subset_1(A_174, A_174)='#skF_9' | ~r1_tarski(k3_subset_1(A_174, A_174), A_174))), inference(demodulation, [status(thm), theory('equality')], [c_1496, c_1554])).
% 4.40/1.78  tff(c_1797, plain, (![B_175]: (k3_subset_1(B_175, B_175)='#skF_9' | ~m1_subset_1(B_175, k1_zfmisc_1(B_175)))), inference(resolution, [status(thm)], [c_1343, c_1786])).
% 4.40/1.78  tff(c_1801, plain, (![A_30]: (k3_subset_1(A_30, A_30)='#skF_9' | ~r1_tarski(A_30, A_30))), inference(resolution, [status(thm)], [c_473, c_1797])).
% 4.40/1.78  tff(c_1866, plain, (![A_178]: (k3_subset_1(A_178, A_178)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_313, c_1801])).
% 4.40/1.78  tff(c_814, plain, (![A_123, B_124]: (k3_subset_1(A_123, k3_subset_1(A_123, B_124))=B_124 | ~m1_subset_1(B_124, k1_zfmisc_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.40/1.78  tff(c_828, plain, (![A_30, C_34]: (k3_subset_1(A_30, k3_subset_1(A_30, C_34))=C_34 | ~r1_tarski(C_34, A_30))), inference(resolution, [status(thm)], [c_473, c_814])).
% 4.40/1.78  tff(c_1877, plain, (![A_178]: (k3_subset_1(A_178, '#skF_9')=A_178 | ~r1_tarski(A_178, A_178))), inference(superposition, [status(thm), theory('equality')], [c_1866, c_828])).
% 4.40/1.78  tff(c_1882, plain, (![A_178]: (k3_subset_1(A_178, '#skF_9')=A_178)), inference(demodulation, [status(thm), theory('equality')], [c_313, c_1877])).
% 4.40/1.78  tff(c_1920, plain, (~r1_tarski('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1882, c_129])).
% 4.40/1.78  tff(c_1924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_1920])).
% 4.40/1.78  tff(c_1925, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_86])).
% 4.40/1.78  tff(c_1995, plain, (![A_201, B_202]: (~r2_hidden('#skF_1'(A_201, B_202), B_202) | r1_tarski(A_201, B_202))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.40/1.78  tff(c_2004, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_1995])).
% 4.40/1.78  tff(c_2879, plain, (![A_267, B_268]: (k4_xboole_0(A_267, B_268)=k3_subset_1(A_267, B_268) | ~m1_subset_1(B_268, k1_zfmisc_1(A_267)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.40/1.78  tff(c_2903, plain, (k4_xboole_0('#skF_8', '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_76, c_2879])).
% 4.40/1.78  tff(c_2261, plain, (![A_223, C_224, B_225]: (r1_xboole_0(A_223, k4_xboole_0(C_224, B_225)) | ~r1_tarski(A_223, B_225))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.40/1.78  tff(c_2268, plain, (![A_223, C_224, B_225]: (k3_xboole_0(A_223, k4_xboole_0(C_224, B_225))=k1_xboole_0 | ~r1_tarski(A_223, B_225))), inference(resolution, [status(thm)], [c_2261, c_28])).
% 4.40/1.78  tff(c_2934, plain, (![A_270]: (k3_xboole_0(A_270, k3_subset_1('#skF_8', '#skF_9'))=k1_xboole_0 | ~r1_tarski(A_270, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2903, c_2268])).
% 4.40/1.78  tff(c_1926, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_86])).
% 4.40/1.78  tff(c_1956, plain, (![A_193, B_194]: (k3_xboole_0(A_193, B_194)=A_193 | ~r1_tarski(A_193, B_194))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.40/1.78  tff(c_1960, plain, (k3_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))='#skF_9'), inference(resolution, [status(thm)], [c_1926, c_1956])).
% 4.40/1.78  tff(c_2964, plain, (k1_xboole_0='#skF_9' | ~r1_tarski('#skF_9', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2934, c_1960])).
% 4.40/1.78  tff(c_3000, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2004, c_2964])).
% 4.40/1.78  tff(c_3002, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1925, c_3000])).
% 4.40/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/1.78  
% 4.40/1.78  Inference rules
% 4.40/1.78  ----------------------
% 4.40/1.78  #Ref     : 0
% 4.40/1.78  #Sup     : 715
% 4.40/1.78  #Fact    : 0
% 4.40/1.78  #Define  : 0
% 4.40/1.78  #Split   : 7
% 4.40/1.78  #Chain   : 0
% 4.40/1.78  #Close   : 0
% 4.40/1.78  
% 4.40/1.78  Ordering : KBO
% 4.40/1.78  
% 4.40/1.78  Simplification rules
% 4.40/1.78  ----------------------
% 4.40/1.78  #Subsume      : 97
% 4.40/1.78  #Demod        : 133
% 4.40/1.78  #Tautology    : 271
% 4.40/1.78  #SimpNegUnit  : 15
% 4.40/1.78  #BackRed      : 29
% 4.40/1.78  
% 4.40/1.78  #Partial instantiations: 0
% 4.40/1.78  #Strategies tried      : 1
% 4.40/1.78  
% 4.40/1.78  Timing (in seconds)
% 4.40/1.78  ----------------------
% 4.40/1.78  Preprocessing        : 0.33
% 4.40/1.78  Parsing              : 0.17
% 4.40/1.78  CNF conversion       : 0.03
% 4.40/1.78  Main loop            : 0.68
% 4.40/1.78  Inferencing          : 0.25
% 4.40/1.78  Reduction            : 0.21
% 4.40/1.78  Demodulation         : 0.14
% 4.40/1.78  BG Simplification    : 0.03
% 4.40/1.78  Subsumption          : 0.13
% 4.40/1.78  Abstraction          : 0.03
% 4.40/1.78  MUC search           : 0.00
% 4.40/1.78  Cooper               : 0.00
% 4.40/1.78  Total                : 1.05
% 4.40/1.78  Index Insertion      : 0.00
% 4.40/1.78  Index Deletion       : 0.00
% 4.40/1.78  Index Matching       : 0.00
% 4.40/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
