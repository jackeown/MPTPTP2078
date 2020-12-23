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
% DateTime   : Thu Dec  3 10:06:19 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 139 expanded)
%              Number of leaves         :   38 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  130 ( 264 expanded)
%              Number of equality atoms :   15 (  32 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_7 > #skF_1 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_6 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_109,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_133,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_99,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_116,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_130,plain,(
    v3_ordinal1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2226,plain,(
    ! [A_5886,B_5887] :
      ( r1_ordinal1(A_5886,B_5887)
      | ~ r1_tarski(A_5886,B_5887)
      | ~ v3_ordinal1(B_5887)
      | ~ v3_ordinal1(A_5886) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2242,plain,(
    ! [B_8] :
      ( r1_ordinal1(B_8,B_8)
      | ~ v3_ordinal1(B_8) ) ),
    inference(resolution,[status(thm)],[c_24,c_2226])).

tff(c_28,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_114,plain,(
    ! [A_59] : k2_xboole_0(A_59,k1_tarski(A_59)) = k1_ordinal1(A_59) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_272,plain,(
    ! [D_96,B_97,A_98] :
      ( ~ r2_hidden(D_96,B_97)
      | r2_hidden(D_96,k2_xboole_0(A_98,B_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_292,plain,(
    ! [D_102,A_103] :
      ( ~ r2_hidden(D_102,k1_tarski(A_103))
      | r2_hidden(D_102,k1_ordinal1(A_103)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_272])).

tff(c_301,plain,(
    ! [C_13] : r2_hidden(C_13,k1_ordinal1(C_13)) ),
    inference(resolution,[status(thm)],[c_28,c_292])).

tff(c_128,plain,(
    v3_ordinal1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_338,plain,(
    ! [B_112,A_113] :
      ( r2_hidden(B_112,A_113)
      | r1_ordinal1(A_113,B_112)
      | ~ v3_ordinal1(B_112)
      | ~ v3_ordinal1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_232,plain,(
    ! [D_86,A_87,B_88] :
      ( ~ r2_hidden(D_86,A_87)
      | r2_hidden(D_86,k2_xboole_0(A_87,B_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_239,plain,(
    ! [D_89,A_90] :
      ( ~ r2_hidden(D_89,A_90)
      | r2_hidden(D_89,k1_ordinal1(A_90)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_232])).

tff(c_132,plain,
    ( ~ r1_ordinal1('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_8',k1_ordinal1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_160,plain,(
    ~ r2_hidden('#skF_8',k1_ordinal1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_243,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_239,c_160])).

tff(c_348,plain,
    ( r1_ordinal1('#skF_9','#skF_8')
    | ~ v3_ordinal1('#skF_8')
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_338,c_243])).

tff(c_360,plain,(
    r1_ordinal1('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_130,c_348])).

tff(c_138,plain,
    ( r2_hidden('#skF_8',k1_ordinal1('#skF_9'))
    | r1_ordinal1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_192,plain,(
    r1_ordinal1('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_138])).

tff(c_124,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | ~ r1_ordinal1(A_64,B_65)
      | ~ v3_ordinal1(B_65)
      | ~ v3_ordinal1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_366,plain,(
    ! [A_114,B_115] :
      ( r1_tarski(A_114,B_115)
      | ~ r1_ordinal1(A_114,B_115)
      | ~ v3_ordinal1(B_115)
      | ~ v3_ordinal1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1835,plain,(
    ! [B_5419,A_5420] :
      ( B_5419 = A_5420
      | ~ r1_tarski(B_5419,A_5420)
      | ~ r1_ordinal1(A_5420,B_5419)
      | ~ v3_ordinal1(B_5419)
      | ~ v3_ordinal1(A_5420) ) ),
    inference(resolution,[status(thm)],[c_366,c_20])).

tff(c_2009,plain,(
    ! [B_5778,A_5779] :
      ( B_5778 = A_5779
      | ~ r1_ordinal1(B_5778,A_5779)
      | ~ r1_ordinal1(A_5779,B_5778)
      | ~ v3_ordinal1(B_5778)
      | ~ v3_ordinal1(A_5779) ) ),
    inference(resolution,[status(thm)],[c_124,c_1835])).

tff(c_2023,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r1_ordinal1('#skF_9','#skF_8')
    | ~ v3_ordinal1('#skF_8')
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_192,c_2009])).

tff(c_2035,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_130,c_360,c_2023])).

tff(c_2043,plain,(
    ~ r2_hidden('#skF_8',k1_ordinal1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2035,c_160])).

tff(c_2049,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_2043])).

tff(c_2050,plain,(
    ~ r1_ordinal1('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_142,plain,(
    ! [A_72] :
      ( v1_ordinal1(A_72)
      | ~ v3_ordinal1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_149,plain,(
    v1_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_128,c_142])).

tff(c_2051,plain,(
    r2_hidden('#skF_8',k1_ordinal1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_2311,plain,(
    ! [D_5897,B_5898,A_5899] :
      ( r2_hidden(D_5897,B_5898)
      | r2_hidden(D_5897,A_5899)
      | ~ r2_hidden(D_5897,k2_xboole_0(A_5899,B_5898)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3019,plain,(
    ! [D_9907,A_9908] :
      ( r2_hidden(D_9907,k1_tarski(A_9908))
      | r2_hidden(D_9907,A_9908)
      | ~ r2_hidden(D_9907,k1_ordinal1(A_9908)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_2311])).

tff(c_26,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3084,plain,(
    ! [D_9978,A_9979] :
      ( D_9978 = A_9979
      | r2_hidden(D_9978,A_9979)
      | ~ r2_hidden(D_9978,k1_ordinal1(A_9979)) ) ),
    inference(resolution,[status(thm)],[c_3019,c_26])).

tff(c_3112,plain,
    ( '#skF_9' = '#skF_8'
    | r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_2051,c_3084])).

tff(c_3113,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_3112])).

tff(c_116,plain,(
    ! [B_63,A_60] :
      ( r1_tarski(B_63,A_60)
      | ~ r2_hidden(B_63,A_60)
      | ~ v1_ordinal1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3116,plain,
    ( r1_tarski('#skF_8','#skF_9')
    | ~ v1_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_3113,c_116])).

tff(c_3119,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_3116])).

tff(c_122,plain,(
    ! [A_64,B_65] :
      ( r1_ordinal1(A_64,B_65)
      | ~ r1_tarski(A_64,B_65)
      | ~ v3_ordinal1(B_65)
      | ~ v3_ordinal1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3122,plain,
    ( r1_ordinal1('#skF_8','#skF_9')
    | ~ v3_ordinal1('#skF_9')
    | ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_3119,c_122])).

tff(c_3127,plain,(
    r1_ordinal1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_128,c_3122])).

tff(c_3129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2050,c_3127])).

tff(c_3130,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3112])).

tff(c_3136,plain,(
    ~ r1_ordinal1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3130,c_2050])).

tff(c_3160,plain,(
    ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_2242,c_3136])).

tff(c_3166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_3160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:34:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.87  
% 4.80/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.88  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_7 > #skF_1 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_6 > #skF_5 > #skF_4
% 4.80/1.88  
% 4.80/1.88  %Foreground sorts:
% 4.80/1.88  
% 4.80/1.88  
% 4.80/1.88  %Background operators:
% 4.80/1.88  
% 4.80/1.88  
% 4.80/1.88  %Foreground operators:
% 4.80/1.88  tff('#skF_7', type, '#skF_7': $i > $i).
% 4.80/1.88  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.80/1.88  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 4.80/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.80/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.80/1.88  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 4.80/1.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.80/1.88  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.80/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.80/1.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.80/1.88  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 4.80/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.80/1.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.80/1.88  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.80/1.88  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 4.80/1.88  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.80/1.88  tff('#skF_9', type, '#skF_9': $i).
% 4.80/1.88  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 4.80/1.88  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.80/1.88  tff('#skF_8', type, '#skF_8': $i).
% 4.80/1.88  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.80/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/1.88  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.80/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/1.88  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.80/1.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.80/1.88  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.80/1.88  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.80/1.88  
% 4.80/1.89  tff(f_143, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 4.80/1.89  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.80/1.89  tff(f_124, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 4.80/1.89  tff(f_47, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.80/1.89  tff(f_109, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 4.80/1.89  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.80/1.89  tff(f_133, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 4.80/1.89  tff(f_99, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 4.80/1.89  tff(f_116, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 4.80/1.89  tff(c_130, plain, (v3_ordinal1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.80/1.89  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.80/1.89  tff(c_2226, plain, (![A_5886, B_5887]: (r1_ordinal1(A_5886, B_5887) | ~r1_tarski(A_5886, B_5887) | ~v3_ordinal1(B_5887) | ~v3_ordinal1(A_5886))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.80/1.89  tff(c_2242, plain, (![B_8]: (r1_ordinal1(B_8, B_8) | ~v3_ordinal1(B_8))), inference(resolution, [status(thm)], [c_24, c_2226])).
% 4.80/1.89  tff(c_28, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.80/1.89  tff(c_114, plain, (![A_59]: (k2_xboole_0(A_59, k1_tarski(A_59))=k1_ordinal1(A_59))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.80/1.89  tff(c_272, plain, (![D_96, B_97, A_98]: (~r2_hidden(D_96, B_97) | r2_hidden(D_96, k2_xboole_0(A_98, B_97)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.80/1.89  tff(c_292, plain, (![D_102, A_103]: (~r2_hidden(D_102, k1_tarski(A_103)) | r2_hidden(D_102, k1_ordinal1(A_103)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_272])).
% 4.80/1.89  tff(c_301, plain, (![C_13]: (r2_hidden(C_13, k1_ordinal1(C_13)))), inference(resolution, [status(thm)], [c_28, c_292])).
% 4.80/1.89  tff(c_128, plain, (v3_ordinal1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.80/1.89  tff(c_338, plain, (![B_112, A_113]: (r2_hidden(B_112, A_113) | r1_ordinal1(A_113, B_112) | ~v3_ordinal1(B_112) | ~v3_ordinal1(A_113))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.80/1.89  tff(c_232, plain, (![D_86, A_87, B_88]: (~r2_hidden(D_86, A_87) | r2_hidden(D_86, k2_xboole_0(A_87, B_88)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.80/1.89  tff(c_239, plain, (![D_89, A_90]: (~r2_hidden(D_89, A_90) | r2_hidden(D_89, k1_ordinal1(A_90)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_232])).
% 4.80/1.89  tff(c_132, plain, (~r1_ordinal1('#skF_8', '#skF_9') | ~r2_hidden('#skF_8', k1_ordinal1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.80/1.89  tff(c_160, plain, (~r2_hidden('#skF_8', k1_ordinal1('#skF_9'))), inference(splitLeft, [status(thm)], [c_132])).
% 4.80/1.89  tff(c_243, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_239, c_160])).
% 4.80/1.89  tff(c_348, plain, (r1_ordinal1('#skF_9', '#skF_8') | ~v3_ordinal1('#skF_8') | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_338, c_243])).
% 4.80/1.89  tff(c_360, plain, (r1_ordinal1('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_130, c_348])).
% 4.80/1.89  tff(c_138, plain, (r2_hidden('#skF_8', k1_ordinal1('#skF_9')) | r1_ordinal1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.80/1.89  tff(c_192, plain, (r1_ordinal1('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_160, c_138])).
% 4.80/1.89  tff(c_124, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | ~r1_ordinal1(A_64, B_65) | ~v3_ordinal1(B_65) | ~v3_ordinal1(A_64))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.80/1.89  tff(c_366, plain, (![A_114, B_115]: (r1_tarski(A_114, B_115) | ~r1_ordinal1(A_114, B_115) | ~v3_ordinal1(B_115) | ~v3_ordinal1(A_114))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.80/1.89  tff(c_20, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.80/1.89  tff(c_1835, plain, (![B_5419, A_5420]: (B_5419=A_5420 | ~r1_tarski(B_5419, A_5420) | ~r1_ordinal1(A_5420, B_5419) | ~v3_ordinal1(B_5419) | ~v3_ordinal1(A_5420))), inference(resolution, [status(thm)], [c_366, c_20])).
% 4.80/1.89  tff(c_2009, plain, (![B_5778, A_5779]: (B_5778=A_5779 | ~r1_ordinal1(B_5778, A_5779) | ~r1_ordinal1(A_5779, B_5778) | ~v3_ordinal1(B_5778) | ~v3_ordinal1(A_5779))), inference(resolution, [status(thm)], [c_124, c_1835])).
% 4.80/1.89  tff(c_2023, plain, ('#skF_9'='#skF_8' | ~r1_ordinal1('#skF_9', '#skF_8') | ~v3_ordinal1('#skF_8') | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_192, c_2009])).
% 4.80/1.89  tff(c_2035, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_130, c_360, c_2023])).
% 4.80/1.89  tff(c_2043, plain, (~r2_hidden('#skF_8', k1_ordinal1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2035, c_160])).
% 4.80/1.89  tff(c_2049, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_301, c_2043])).
% 4.80/1.89  tff(c_2050, plain, (~r1_ordinal1('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_132])).
% 4.80/1.89  tff(c_142, plain, (![A_72]: (v1_ordinal1(A_72) | ~v3_ordinal1(A_72))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.80/1.89  tff(c_149, plain, (v1_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_128, c_142])).
% 4.80/1.89  tff(c_2051, plain, (r2_hidden('#skF_8', k1_ordinal1('#skF_9'))), inference(splitRight, [status(thm)], [c_132])).
% 4.80/1.89  tff(c_2311, plain, (![D_5897, B_5898, A_5899]: (r2_hidden(D_5897, B_5898) | r2_hidden(D_5897, A_5899) | ~r2_hidden(D_5897, k2_xboole_0(A_5899, B_5898)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.80/1.89  tff(c_3019, plain, (![D_9907, A_9908]: (r2_hidden(D_9907, k1_tarski(A_9908)) | r2_hidden(D_9907, A_9908) | ~r2_hidden(D_9907, k1_ordinal1(A_9908)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_2311])).
% 4.80/1.89  tff(c_26, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.80/1.89  tff(c_3084, plain, (![D_9978, A_9979]: (D_9978=A_9979 | r2_hidden(D_9978, A_9979) | ~r2_hidden(D_9978, k1_ordinal1(A_9979)))), inference(resolution, [status(thm)], [c_3019, c_26])).
% 4.80/1.89  tff(c_3112, plain, ('#skF_9'='#skF_8' | r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_2051, c_3084])).
% 4.80/1.89  tff(c_3113, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_3112])).
% 4.80/1.89  tff(c_116, plain, (![B_63, A_60]: (r1_tarski(B_63, A_60) | ~r2_hidden(B_63, A_60) | ~v1_ordinal1(A_60))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.80/1.89  tff(c_3116, plain, (r1_tarski('#skF_8', '#skF_9') | ~v1_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_3113, c_116])).
% 4.80/1.89  tff(c_3119, plain, (r1_tarski('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_3116])).
% 4.80/1.89  tff(c_122, plain, (![A_64, B_65]: (r1_ordinal1(A_64, B_65) | ~r1_tarski(A_64, B_65) | ~v3_ordinal1(B_65) | ~v3_ordinal1(A_64))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.80/1.89  tff(c_3122, plain, (r1_ordinal1('#skF_8', '#skF_9') | ~v3_ordinal1('#skF_9') | ~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_3119, c_122])).
% 4.80/1.89  tff(c_3127, plain, (r1_ordinal1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_128, c_3122])).
% 4.80/1.89  tff(c_3129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2050, c_3127])).
% 4.80/1.89  tff(c_3130, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_3112])).
% 4.80/1.89  tff(c_3136, plain, (~r1_ordinal1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3130, c_2050])).
% 4.80/1.89  tff(c_3160, plain, (~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_2242, c_3136])).
% 4.80/1.89  tff(c_3166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_3160])).
% 4.80/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.80/1.89  
% 4.80/1.89  Inference rules
% 4.80/1.89  ----------------------
% 4.80/1.89  #Ref     : 0
% 4.80/1.89  #Sup     : 342
% 4.80/1.89  #Fact    : 4
% 4.80/1.89  #Define  : 0
% 4.80/1.89  #Split   : 5
% 4.80/1.89  #Chain   : 0
% 4.80/1.89  #Close   : 0
% 4.80/1.89  
% 4.80/1.89  Ordering : KBO
% 4.80/1.89  
% 4.80/1.89  Simplification rules
% 4.80/1.89  ----------------------
% 4.80/1.89  #Subsume      : 24
% 4.80/1.89  #Demod        : 74
% 4.80/1.89  #Tautology    : 84
% 4.80/1.89  #SimpNegUnit  : 3
% 4.80/1.89  #BackRed      : 18
% 4.80/1.89  
% 4.80/1.89  #Partial instantiations: 2880
% 4.80/1.89  #Strategies tried      : 1
% 4.80/1.89  
% 4.80/1.89  Timing (in seconds)
% 4.80/1.89  ----------------------
% 4.80/1.89  Preprocessing        : 0.37
% 4.80/1.89  Parsing              : 0.17
% 4.80/1.89  CNF conversion       : 0.03
% 4.80/1.89  Main loop            : 0.69
% 4.80/1.89  Inferencing          : 0.33
% 4.80/1.89  Reduction            : 0.15
% 4.80/1.89  Demodulation         : 0.11
% 4.80/1.89  BG Simplification    : 0.04
% 4.80/1.89  Subsumption          : 0.13
% 4.80/1.89  Abstraction          : 0.04
% 4.80/1.89  MUC search           : 0.00
% 4.80/1.89  Cooper               : 0.00
% 4.80/1.89  Total                : 1.09
% 4.80/1.89  Index Insertion      : 0.00
% 4.80/1.89  Index Deletion       : 0.00
% 4.80/1.89  Index Matching       : 0.00
% 4.80/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
