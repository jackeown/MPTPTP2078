%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:23 EST 2020

% Result     : Theorem 5.82s
% Output     : CNFRefutation 5.82s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 142 expanded)
%              Number of leaves         :   32 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  120 ( 228 expanded)
%              Number of equality atoms :   52 (  88 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_83,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(c_28,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_80,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = k1_xboole_0
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_92,plain,(
    ! [B_11] : k4_xboole_0(B_11,B_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_80])).

tff(c_219,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_248,plain,(
    ! [B_11] : k4_xboole_0(B_11,k1_xboole_0) = k3_xboole_0(B_11,B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_219])).

tff(c_258,plain,(
    ! [B_11] : k3_xboole_0(B_11,B_11) = B_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_248])).

tff(c_297,plain,(
    ! [A_68,B_69] : k2_xboole_0(k3_xboole_0(A_68,B_69),k4_xboole_0(A_68,B_69)) = A_68 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_324,plain,(
    ! [B_11] : k2_xboole_0(k3_xboole_0(B_11,B_11),k1_xboole_0) = B_11 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_297])).

tff(c_352,plain,(
    ! [B_71] : k2_xboole_0(B_71,k1_xboole_0) = B_71 ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_324])).

tff(c_22,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_tarski(A_14,k2_xboole_0(C_16,B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_399,plain,(
    ! [A_80,B_81] :
      ( r1_tarski(A_80,B_81)
      | ~ r1_tarski(A_80,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_22])).

tff(c_405,plain,(
    ! [A_12,B_81] :
      ( r1_tarski(A_12,B_81)
      | k4_xboole_0(A_12,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_399])).

tff(c_426,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(A_82,B_83)
      | k1_xboole_0 != A_82 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_405])).

tff(c_44,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_438,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(resolution,[status(thm)],[c_426,c_44])).

tff(c_736,plain,(
    ! [A_112,A_113,B_114] :
      ( r1_tarski(A_112,A_113)
      | ~ r1_tarski(A_112,k4_xboole_0(A_113,B_114)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_22])).

tff(c_806,plain,(
    ! [A_117,B_118] : r1_tarski(k4_xboole_0(A_117,B_118),A_117) ),
    inference(resolution,[status(thm)],[c_16,c_736])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_853,plain,(
    ! [A_117,B_118] : k4_xboole_0(k4_xboole_0(A_117,B_118),A_117) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_806,c_20])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_48,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_780,plain,(
    ! [B_115,A_116] :
      ( B_115 = A_116
      | ~ r1_tarski(A_116,B_115)
      | ~ v1_zfmisc_1(B_115)
      | v1_xboole_0(B_115)
      | v1_xboole_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_7338,plain,(
    ! [B_291,A_292] :
      ( B_291 = A_292
      | ~ v1_zfmisc_1(B_291)
      | v1_xboole_0(B_291)
      | v1_xboole_0(A_292)
      | k4_xboole_0(A_292,B_291) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_780])).

tff(c_7340,plain,(
    ! [A_292] :
      ( A_292 = '#skF_3'
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_292)
      | k4_xboole_0(A_292,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_48,c_7338])).

tff(c_7344,plain,(
    ! [A_293] :
      ( A_293 = '#skF_3'
      | v1_xboole_0(A_293)
      | k4_xboole_0(A_293,'#skF_3') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_7340])).

tff(c_24,plain,(
    ! [A_17,B_18] : r1_tarski(k3_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_940,plain,(
    ! [A_123,B_124,B_125] : r1_tarski(k3_xboole_0(k4_xboole_0(A_123,B_124),B_125),A_123) ),
    inference(resolution,[status(thm)],[c_24,c_736])).

tff(c_374,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_2'(A_72,B_73),A_72)
      | r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_378,plain,(
    ! [A_72,B_73] :
      ( ~ v1_xboole_0(A_72)
      | r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_374,c_2])).

tff(c_439,plain,(
    ! [B_84,A_85] :
      ( B_84 = A_85
      | ~ r1_tarski(B_84,A_85)
      | ~ r1_tarski(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_453,plain,(
    ! [B_73,A_72] :
      ( B_73 = A_72
      | ~ r1_tarski(B_73,A_72)
      | ~ v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_378,c_439])).

tff(c_1673,plain,(
    ! [A_148,B_149,B_150] :
      ( k3_xboole_0(k4_xboole_0(A_148,B_149),B_150) = A_148
      | ~ v1_xboole_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_940,c_453])).

tff(c_26,plain,(
    ! [A_19] : k3_xboole_0(A_19,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1716,plain,(
    ! [A_148] :
      ( k1_xboole_0 = A_148
      | ~ v1_xboole_0(A_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1673,c_26])).

tff(c_7386,plain,(
    ! [A_294] :
      ( k1_xboole_0 = A_294
      | A_294 = '#skF_3'
      | k4_xboole_0(A_294,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_7344,c_1716])).

tff(c_7528,plain,(
    ! [B_297] :
      ( k4_xboole_0('#skF_3',B_297) = k1_xboole_0
      | k4_xboole_0('#skF_3',B_297) = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_853,c_7386])).

tff(c_154,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | k4_xboole_0(A_53,B_54) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_162,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_154,c_44])).

tff(c_7731,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7528,c_162])).

tff(c_5969,plain,(
    ! [A_263,B_264] :
      ( k3_xboole_0(A_263,B_264) = A_263
      | ~ v1_zfmisc_1(A_263)
      | v1_xboole_0(A_263)
      | v1_xboole_0(k3_xboole_0(A_263,B_264)) ) ),
    inference(resolution,[status(thm)],[c_24,c_780])).

tff(c_46,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5995,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5969,c_46])).

tff(c_6039,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_5995])).

tff(c_6040,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_6039])).

tff(c_30,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_222,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,k4_xboole_0(A_65,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_30])).

tff(c_6080,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k4_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6040,c_222])).

tff(c_6136,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_6080])).

tff(c_7750,plain,(
    k3_xboole_0('#skF_3','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7731,c_6136])).

tff(c_7752,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_7750])).

tff(c_7754,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_438,c_7752])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.82/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.82/2.12  
% 5.82/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.82/2.12  %$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 5.82/2.12  
% 5.82/2.12  %Foreground sorts:
% 5.82/2.12  
% 5.82/2.12  
% 5.82/2.12  %Background operators:
% 5.82/2.12  
% 5.82/2.12  
% 5.82/2.12  %Foreground operators:
% 5.82/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.82/2.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.82/2.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.82/2.12  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.82/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.82/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.82/2.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.82/2.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.82/2.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.82/2.12  tff('#skF_3', type, '#skF_3': $i).
% 5.82/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.82/2.12  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.82/2.12  tff('#skF_4', type, '#skF_4': $i).
% 5.82/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.82/2.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.82/2.12  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.82/2.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.82/2.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.82/2.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.82/2.12  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.82/2.12  
% 5.82/2.14  tff(f_58, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.82/2.14  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.82/2.14  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.82/2.14  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.82/2.14  tff(f_62, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.82/2.14  tff(f_52, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 5.82/2.14  tff(f_95, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 5.82/2.14  tff(f_83, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 5.82/2.14  tff(f_54, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.82/2.14  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.82/2.14  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.82/2.14  tff(f_56, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.82/2.14  tff(c_28, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.82/2.14  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | k4_xboole_0(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.82/2.14  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.82/2.14  tff(c_80, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=k1_xboole_0 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.82/2.14  tff(c_92, plain, (![B_11]: (k4_xboole_0(B_11, B_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_80])).
% 5.82/2.14  tff(c_219, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.82/2.14  tff(c_248, plain, (![B_11]: (k4_xboole_0(B_11, k1_xboole_0)=k3_xboole_0(B_11, B_11))), inference(superposition, [status(thm), theory('equality')], [c_92, c_219])).
% 5.82/2.14  tff(c_258, plain, (![B_11]: (k3_xboole_0(B_11, B_11)=B_11)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_248])).
% 5.82/2.14  tff(c_297, plain, (![A_68, B_69]: (k2_xboole_0(k3_xboole_0(A_68, B_69), k4_xboole_0(A_68, B_69))=A_68)), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.82/2.14  tff(c_324, plain, (![B_11]: (k2_xboole_0(k3_xboole_0(B_11, B_11), k1_xboole_0)=B_11)), inference(superposition, [status(thm), theory('equality')], [c_92, c_297])).
% 5.82/2.14  tff(c_352, plain, (![B_71]: (k2_xboole_0(B_71, k1_xboole_0)=B_71)), inference(demodulation, [status(thm), theory('equality')], [c_258, c_324])).
% 5.82/2.14  tff(c_22, plain, (![A_14, C_16, B_15]: (r1_tarski(A_14, k2_xboole_0(C_16, B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.82/2.14  tff(c_399, plain, (![A_80, B_81]: (r1_tarski(A_80, B_81) | ~r1_tarski(A_80, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_352, c_22])).
% 5.82/2.14  tff(c_405, plain, (![A_12, B_81]: (r1_tarski(A_12, B_81) | k4_xboole_0(A_12, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_399])).
% 5.82/2.14  tff(c_426, plain, (![A_82, B_83]: (r1_tarski(A_82, B_83) | k1_xboole_0!=A_82)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_405])).
% 5.82/2.14  tff(c_44, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.82/2.14  tff(c_438, plain, (k1_xboole_0!='#skF_3'), inference(resolution, [status(thm)], [c_426, c_44])).
% 5.82/2.14  tff(c_736, plain, (![A_112, A_113, B_114]: (r1_tarski(A_112, A_113) | ~r1_tarski(A_112, k4_xboole_0(A_113, B_114)))), inference(superposition, [status(thm), theory('equality')], [c_297, c_22])).
% 5.82/2.14  tff(c_806, plain, (![A_117, B_118]: (r1_tarski(k4_xboole_0(A_117, B_118), A_117))), inference(resolution, [status(thm)], [c_16, c_736])).
% 5.82/2.14  tff(c_20, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.82/2.14  tff(c_853, plain, (![A_117, B_118]: (k4_xboole_0(k4_xboole_0(A_117, B_118), A_117)=k1_xboole_0)), inference(resolution, [status(thm)], [c_806, c_20])).
% 5.82/2.14  tff(c_50, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.82/2.14  tff(c_48, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.82/2.14  tff(c_780, plain, (![B_115, A_116]: (B_115=A_116 | ~r1_tarski(A_116, B_115) | ~v1_zfmisc_1(B_115) | v1_xboole_0(B_115) | v1_xboole_0(A_116))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.82/2.14  tff(c_7338, plain, (![B_291, A_292]: (B_291=A_292 | ~v1_zfmisc_1(B_291) | v1_xboole_0(B_291) | v1_xboole_0(A_292) | k4_xboole_0(A_292, B_291)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_780])).
% 5.82/2.14  tff(c_7340, plain, (![A_292]: (A_292='#skF_3' | v1_xboole_0('#skF_3') | v1_xboole_0(A_292) | k4_xboole_0(A_292, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_7338])).
% 5.82/2.14  tff(c_7344, plain, (![A_293]: (A_293='#skF_3' | v1_xboole_0(A_293) | k4_xboole_0(A_293, '#skF_3')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_50, c_7340])).
% 5.82/2.14  tff(c_24, plain, (![A_17, B_18]: (r1_tarski(k3_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.82/2.14  tff(c_940, plain, (![A_123, B_124, B_125]: (r1_tarski(k3_xboole_0(k4_xboole_0(A_123, B_124), B_125), A_123))), inference(resolution, [status(thm)], [c_24, c_736])).
% 5.82/2.14  tff(c_374, plain, (![A_72, B_73]: (r2_hidden('#skF_2'(A_72, B_73), A_72) | r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.82/2.14  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.82/2.14  tff(c_378, plain, (![A_72, B_73]: (~v1_xboole_0(A_72) | r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_374, c_2])).
% 5.82/2.14  tff(c_439, plain, (![B_84, A_85]: (B_84=A_85 | ~r1_tarski(B_84, A_85) | ~r1_tarski(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.82/2.14  tff(c_453, plain, (![B_73, A_72]: (B_73=A_72 | ~r1_tarski(B_73, A_72) | ~v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_378, c_439])).
% 5.82/2.14  tff(c_1673, plain, (![A_148, B_149, B_150]: (k3_xboole_0(k4_xboole_0(A_148, B_149), B_150)=A_148 | ~v1_xboole_0(A_148))), inference(resolution, [status(thm)], [c_940, c_453])).
% 5.82/2.14  tff(c_26, plain, (![A_19]: (k3_xboole_0(A_19, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.82/2.14  tff(c_1716, plain, (![A_148]: (k1_xboole_0=A_148 | ~v1_xboole_0(A_148))), inference(superposition, [status(thm), theory('equality')], [c_1673, c_26])).
% 5.82/2.14  tff(c_7386, plain, (![A_294]: (k1_xboole_0=A_294 | A_294='#skF_3' | k4_xboole_0(A_294, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_7344, c_1716])).
% 5.82/2.14  tff(c_7528, plain, (![B_297]: (k4_xboole_0('#skF_3', B_297)=k1_xboole_0 | k4_xboole_0('#skF_3', B_297)='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_853, c_7386])).
% 5.82/2.14  tff(c_154, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | k4_xboole_0(A_53, B_54)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.82/2.14  tff(c_162, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_154, c_44])).
% 5.82/2.14  tff(c_7731, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_7528, c_162])).
% 5.82/2.14  tff(c_5969, plain, (![A_263, B_264]: (k3_xboole_0(A_263, B_264)=A_263 | ~v1_zfmisc_1(A_263) | v1_xboole_0(A_263) | v1_xboole_0(k3_xboole_0(A_263, B_264)))), inference(resolution, [status(thm)], [c_24, c_780])).
% 5.82/2.14  tff(c_46, plain, (~v1_xboole_0(k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.82/2.14  tff(c_5995, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_5969, c_46])).
% 5.82/2.14  tff(c_6039, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3' | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_5995])).
% 5.82/2.14  tff(c_6040, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_50, c_6039])).
% 5.82/2.14  tff(c_30, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.82/2.14  tff(c_222, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k3_xboole_0(A_65, k4_xboole_0(A_65, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_219, c_30])).
% 5.82/2.14  tff(c_6080, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k4_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6040, c_222])).
% 5.82/2.14  tff(c_6136, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_92, c_6080])).
% 5.82/2.14  tff(c_7750, plain, (k3_xboole_0('#skF_3', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7731, c_6136])).
% 5.82/2.14  tff(c_7752, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_258, c_7750])).
% 5.82/2.14  tff(c_7754, plain, $false, inference(negUnitSimplification, [status(thm)], [c_438, c_7752])).
% 5.82/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.82/2.14  
% 5.82/2.14  Inference rules
% 5.82/2.14  ----------------------
% 5.82/2.14  #Ref     : 3
% 5.82/2.14  #Sup     : 1980
% 5.82/2.14  #Fact    : 1
% 5.82/2.14  #Define  : 0
% 5.82/2.14  #Split   : 2
% 5.82/2.14  #Chain   : 0
% 5.82/2.14  #Close   : 0
% 5.82/2.14  
% 5.82/2.14  Ordering : KBO
% 5.82/2.14  
% 5.82/2.14  Simplification rules
% 5.82/2.14  ----------------------
% 5.82/2.14  #Subsume      : 675
% 5.82/2.14  #Demod        : 966
% 5.82/2.14  #Tautology    : 842
% 5.82/2.14  #SimpNegUnit  : 52
% 5.82/2.14  #BackRed      : 13
% 5.82/2.14  
% 5.82/2.14  #Partial instantiations: 0
% 5.82/2.14  #Strategies tried      : 1
% 5.82/2.14  
% 5.82/2.14  Timing (in seconds)
% 5.82/2.14  ----------------------
% 5.82/2.14  Preprocessing        : 0.31
% 5.82/2.14  Parsing              : 0.17
% 5.82/2.14  CNF conversion       : 0.02
% 5.82/2.14  Main loop            : 1.07
% 5.82/2.14  Inferencing          : 0.33
% 5.82/2.14  Reduction            : 0.40
% 5.82/2.14  Demodulation         : 0.31
% 5.82/2.14  BG Simplification    : 0.04
% 5.82/2.14  Subsumption          : 0.23
% 5.82/2.14  Abstraction          : 0.06
% 5.82/2.14  MUC search           : 0.00
% 5.82/2.14  Cooper               : 0.00
% 5.82/2.14  Total                : 1.41
% 5.82/2.14  Index Insertion      : 0.00
% 5.82/2.14  Index Deletion       : 0.00
% 5.82/2.14  Index Matching       : 0.00
% 5.82/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
