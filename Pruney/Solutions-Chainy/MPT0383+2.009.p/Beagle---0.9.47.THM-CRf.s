%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:08 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 385 expanded)
%              Number of leaves         :   22 ( 137 expanded)
%              Depth                    :   13
%              Number of atoms          :  149 ( 956 expanded)
%              Number of equality atoms :    6 (  72 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r2_hidden(D,C)
          & r1_tarski(C,k2_zfmisc_1(A,B))
          & ! [E] :
              ( m1_subset_1(E,A)
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => D != k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(c_30,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_31,plain,(
    ! [B_25,A_26] :
      ( ~ v1_xboole_0(B_25)
      | ~ r2_hidden(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_35,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_31])).

tff(c_42,plain,(
    ! [B_31,A_32] :
      ( m1_subset_1(B_31,A_32)
      | ~ r2_hidden(B_31,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_45,plain,
    ( m1_subset_1('#skF_7','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_42])).

tff(c_48,plain,(
    m1_subset_1('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_45])).

tff(c_69,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_1'(A_39,B_40),A_39)
      | r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_39] : r1_tarski(A_39,A_39) ),
    inference(resolution,[status(thm)],[c_69,c_4])).

tff(c_28,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_85,plain,(
    ! [C_44,B_45,A_46] :
      ( r2_hidden(C_44,B_45)
      | ~ r2_hidden(C_44,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [B_51] :
      ( r2_hidden('#skF_7',B_51)
      | ~ r1_tarski('#skF_6',B_51) ) ),
    inference(resolution,[status(thm)],[c_30,c_85])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_150,plain,(
    ! [B_54,B_55] :
      ( r2_hidden('#skF_7',B_54)
      | ~ r1_tarski(B_55,B_54)
      | ~ r1_tarski('#skF_6',B_55) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_156,plain,
    ( r2_hidden('#skF_7',k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_150])).

tff(c_161,plain,(
    r2_hidden('#skF_7',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_156])).

tff(c_230,plain,(
    ! [A_73,B_74,C_75] :
      ( k4_tarski('#skF_2'(A_73,B_74,C_75),'#skF_3'(A_73,B_74,C_75)) = A_73
      | ~ r2_hidden(A_73,k2_zfmisc_1(B_74,C_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    ! [E_22,F_24] :
      ( k4_tarski(E_22,F_24) != '#skF_7'
      | ~ m1_subset_1(F_24,'#skF_5')
      | ~ m1_subset_1(E_22,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_370,plain,(
    ! [A_97,B_98,C_99] :
      ( A_97 != '#skF_7'
      | ~ m1_subset_1('#skF_3'(A_97,B_98,C_99),'#skF_5')
      | ~ m1_subset_1('#skF_2'(A_97,B_98,C_99),'#skF_4')
      | ~ r2_hidden(A_97,k2_zfmisc_1(B_98,C_99)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_26])).

tff(c_399,plain,
    ( ~ m1_subset_1('#skF_3'('#skF_7','#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_161,c_370])).

tff(c_415,plain,(
    ~ m1_subset_1('#skF_2'('#skF_7','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_399])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( r2_hidden(B_18,A_17)
      | ~ m1_subset_1(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_277,plain,(
    ! [B_82,B_83,A_84] :
      ( r2_hidden(B_82,B_83)
      | ~ r1_tarski(A_84,B_83)
      | ~ m1_subset_1(B_82,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_20,c_85])).

tff(c_283,plain,(
    ! [B_82] :
      ( r2_hidden(B_82,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ m1_subset_1(B_82,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_28,c_277])).

tff(c_288,plain,(
    ! [B_82] :
      ( r2_hidden(B_82,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ m1_subset_1(B_82,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_283])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( m1_subset_1(B_18,A_17)
      | ~ v1_xboole_0(B_18)
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_419,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_7','#skF_4','#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_415])).

tff(c_420,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_419])).

tff(c_16,plain,(
    ! [A_13,C_15,B_14,D_16] :
      ( r2_hidden(A_13,C_15)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_810,plain,(
    ! [C_159,A_160,D_156,B_158,C_157] :
      ( r2_hidden('#skF_2'(A_160,B_158,C_157),C_159)
      | ~ r2_hidden(A_160,k2_zfmisc_1(C_159,D_156))
      | ~ r2_hidden(A_160,k2_zfmisc_1(B_158,C_157)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_16])).

tff(c_863,plain,(
    ! [B_162,C_163] :
      ( r2_hidden('#skF_2'('#skF_7',B_162,C_163),'#skF_4')
      | ~ r2_hidden('#skF_7',k2_zfmisc_1(B_162,C_163)) ) ),
    inference(resolution,[status(thm)],[c_161,c_810])).

tff(c_18,plain,(
    ! [B_18,A_17] :
      ( m1_subset_1(B_18,A_17)
      | ~ r2_hidden(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_868,plain,(
    ! [B_162,C_163] :
      ( m1_subset_1('#skF_2'('#skF_7',B_162,C_163),'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ r2_hidden('#skF_7',k2_zfmisc_1(B_162,C_163)) ) ),
    inference(resolution,[status(thm)],[c_863,c_18])).

tff(c_877,plain,(
    ! [B_164,C_165] :
      ( m1_subset_1('#skF_2'('#skF_7',B_164,C_165),'#skF_4')
      | ~ r2_hidden('#skF_7',k2_zfmisc_1(B_164,C_165)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_420,c_868])).

tff(c_881,plain,
    ( m1_subset_1('#skF_2'('#skF_7','#skF_4','#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_288,c_877])).

tff(c_893,plain,(
    m1_subset_1('#skF_2'('#skF_7','#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_881])).

tff(c_895,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_415,c_893])).

tff(c_897,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_1202,plain,(
    ! [D_204,B_206,C_207,C_205,A_208] :
      ( r2_hidden('#skF_2'(A_208,B_206,C_205),C_207)
      | ~ r2_hidden(A_208,k2_zfmisc_1(C_207,D_204))
      | ~ r2_hidden(A_208,k2_zfmisc_1(B_206,C_205)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_16])).

tff(c_1239,plain,(
    ! [B_209,C_210] :
      ( r2_hidden('#skF_2'('#skF_7',B_209,C_210),'#skF_4')
      | ~ r2_hidden('#skF_7',k2_zfmisc_1(B_209,C_210)) ) ),
    inference(resolution,[status(thm)],[c_161,c_1202])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1247,plain,(
    ! [B_209,C_210] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden('#skF_7',k2_zfmisc_1(B_209,C_210)) ) ),
    inference(resolution,[status(thm)],[c_1239,c_8])).

tff(c_1253,plain,(
    ! [B_209,C_210] : ~ r2_hidden('#skF_7',k2_zfmisc_1(B_209,C_210)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_1247])).

tff(c_1255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1253,c_161])).

tff(c_1256,plain,(
    ~ m1_subset_1('#skF_3'('#skF_7','#skF_4','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_399])).

tff(c_1261,plain,
    ( ~ v1_xboole_0('#skF_3'('#skF_7','#skF_4','#skF_5'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_1256])).

tff(c_1266,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1261])).

tff(c_14,plain,(
    ! [B_14,D_16,A_13,C_15] :
      ( r2_hidden(B_14,D_16)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1424,plain,(
    ! [C_230,A_233,B_231,C_232,D_229] :
      ( r2_hidden('#skF_3'(A_233,B_231,C_230),D_229)
      | ~ r2_hidden(A_233,k2_zfmisc_1(C_232,D_229))
      | ~ r2_hidden(A_233,k2_zfmisc_1(B_231,C_230)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_14])).

tff(c_1453,plain,(
    ! [B_234,C_235] :
      ( r2_hidden('#skF_3'('#skF_7',B_234,C_235),'#skF_5')
      | ~ r2_hidden('#skF_7',k2_zfmisc_1(B_234,C_235)) ) ),
    inference(resolution,[status(thm)],[c_161,c_1424])).

tff(c_1458,plain,(
    ! [B_234,C_235] :
      ( m1_subset_1('#skF_3'('#skF_7',B_234,C_235),'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ r2_hidden('#skF_7',k2_zfmisc_1(B_234,C_235)) ) ),
    inference(resolution,[status(thm)],[c_1453,c_18])).

tff(c_1467,plain,(
    ! [B_236,C_237] :
      ( m1_subset_1('#skF_3'('#skF_7',B_236,C_237),'#skF_5')
      | ~ r2_hidden('#skF_7',k2_zfmisc_1(B_236,C_237)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1266,c_1458])).

tff(c_1471,plain,
    ( m1_subset_1('#skF_3'('#skF_7','#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_288,c_1467])).

tff(c_1483,plain,(
    m1_subset_1('#skF_3'('#skF_7','#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1471])).

tff(c_1485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1256,c_1483])).

tff(c_1487,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1261])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( k4_tarski('#skF_2'(A_8,B_9,C_10),'#skF_3'(A_8,B_9,C_10)) = A_8
      | ~ r2_hidden(A_8,k2_zfmisc_1(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_289,plain,(
    ! [B_85] :
      ( r2_hidden(B_85,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ m1_subset_1(B_85,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_283])).

tff(c_318,plain,(
    ! [B_86,A_87] :
      ( r2_hidden(B_86,'#skF_5')
      | ~ m1_subset_1(k4_tarski(A_87,B_86),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_289,c_14])).

tff(c_1672,plain,(
    ! [A_259,B_260,C_261] :
      ( r2_hidden('#skF_3'(A_259,B_260,C_261),'#skF_5')
      | ~ m1_subset_1(A_259,'#skF_6')
      | ~ r2_hidden(A_259,k2_zfmisc_1(B_260,C_261)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_318])).

tff(c_1680,plain,(
    ! [A_259,B_260,C_261] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_259,'#skF_6')
      | ~ r2_hidden(A_259,k2_zfmisc_1(B_260,C_261)) ) ),
    inference(resolution,[status(thm)],[c_1672,c_8])).

tff(c_1687,plain,(
    ! [A_262,B_263,C_264] :
      ( ~ m1_subset_1(A_262,'#skF_6')
      | ~ r2_hidden(A_262,k2_zfmisc_1(B_263,C_264)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1487,c_1680])).

tff(c_1703,plain,(
    ~ m1_subset_1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_161,c_1687])).

tff(c_1723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1703])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.67  
% 3.69/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.67  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.69/1.67  
% 3.69/1.67  %Foreground sorts:
% 3.69/1.67  
% 3.69/1.67  
% 3.69/1.67  %Background operators:
% 3.69/1.67  
% 3.69/1.67  
% 3.69/1.67  %Foreground operators:
% 3.69/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.69/1.67  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.69/1.67  tff('#skF_7', type, '#skF_7': $i).
% 3.69/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.69/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.69/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.69/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.69/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.69/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.69/1.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.69/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.69/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.69/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.69/1.67  
% 3.69/1.69  tff(f_78, negated_conjecture, ~(![A, B, C, D]: ~((r2_hidden(D, C) & r1_tarski(C, k2_zfmisc_1(A, B))) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => ~(D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_subset_1)).
% 3.69/1.69  tff(f_37, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 3.69/1.69  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.69/1.69  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.69/1.69  tff(f_44, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 3.69/1.69  tff(f_50, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 3.69/1.69  tff(c_30, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.69/1.69  tff(c_31, plain, (![B_25, A_26]: (~v1_xboole_0(B_25) | ~r2_hidden(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.69/1.69  tff(c_35, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_30, c_31])).
% 3.69/1.69  tff(c_42, plain, (![B_31, A_32]: (m1_subset_1(B_31, A_32) | ~r2_hidden(B_31, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.69/1.69  tff(c_45, plain, (m1_subset_1('#skF_7', '#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_30, c_42])).
% 3.69/1.69  tff(c_48, plain, (m1_subset_1('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_35, c_45])).
% 3.69/1.69  tff(c_69, plain, (![A_39, B_40]: (r2_hidden('#skF_1'(A_39, B_40), A_39) | r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.69  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.69  tff(c_80, plain, (![A_39]: (r1_tarski(A_39, A_39))), inference(resolution, [status(thm)], [c_69, c_4])).
% 3.69/1.69  tff(c_28, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.69/1.69  tff(c_85, plain, (![C_44, B_45, A_46]: (r2_hidden(C_44, B_45) | ~r2_hidden(C_44, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.69  tff(c_100, plain, (![B_51]: (r2_hidden('#skF_7', B_51) | ~r1_tarski('#skF_6', B_51))), inference(resolution, [status(thm)], [c_30, c_85])).
% 3.69/1.69  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.69  tff(c_150, plain, (![B_54, B_55]: (r2_hidden('#skF_7', B_54) | ~r1_tarski(B_55, B_54) | ~r1_tarski('#skF_6', B_55))), inference(resolution, [status(thm)], [c_100, c_2])).
% 3.69/1.69  tff(c_156, plain, (r2_hidden('#skF_7', k2_zfmisc_1('#skF_4', '#skF_5')) | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_28, c_150])).
% 3.69/1.69  tff(c_161, plain, (r2_hidden('#skF_7', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_156])).
% 3.69/1.69  tff(c_230, plain, (![A_73, B_74, C_75]: (k4_tarski('#skF_2'(A_73, B_74, C_75), '#skF_3'(A_73, B_74, C_75))=A_73 | ~r2_hidden(A_73, k2_zfmisc_1(B_74, C_75)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.69/1.69  tff(c_26, plain, (![E_22, F_24]: (k4_tarski(E_22, F_24)!='#skF_7' | ~m1_subset_1(F_24, '#skF_5') | ~m1_subset_1(E_22, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.69/1.69  tff(c_370, plain, (![A_97, B_98, C_99]: (A_97!='#skF_7' | ~m1_subset_1('#skF_3'(A_97, B_98, C_99), '#skF_5') | ~m1_subset_1('#skF_2'(A_97, B_98, C_99), '#skF_4') | ~r2_hidden(A_97, k2_zfmisc_1(B_98, C_99)))), inference(superposition, [status(thm), theory('equality')], [c_230, c_26])).
% 3.69/1.69  tff(c_399, plain, (~m1_subset_1('#skF_3'('#skF_7', '#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_2'('#skF_7', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_161, c_370])).
% 3.69/1.69  tff(c_415, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_4', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_399])).
% 3.69/1.69  tff(c_20, plain, (![B_18, A_17]: (r2_hidden(B_18, A_17) | ~m1_subset_1(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.69/1.69  tff(c_277, plain, (![B_82, B_83, A_84]: (r2_hidden(B_82, B_83) | ~r1_tarski(A_84, B_83) | ~m1_subset_1(B_82, A_84) | v1_xboole_0(A_84))), inference(resolution, [status(thm)], [c_20, c_85])).
% 3.69/1.69  tff(c_283, plain, (![B_82]: (r2_hidden(B_82, k2_zfmisc_1('#skF_4', '#skF_5')) | ~m1_subset_1(B_82, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_28, c_277])).
% 3.69/1.69  tff(c_288, plain, (![B_82]: (r2_hidden(B_82, k2_zfmisc_1('#skF_4', '#skF_5')) | ~m1_subset_1(B_82, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_35, c_283])).
% 3.69/1.69  tff(c_22, plain, (![B_18, A_17]: (m1_subset_1(B_18, A_17) | ~v1_xboole_0(B_18) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.69/1.69  tff(c_419, plain, (~v1_xboole_0('#skF_2'('#skF_7', '#skF_4', '#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_22, c_415])).
% 3.69/1.69  tff(c_420, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_419])).
% 3.69/1.69  tff(c_16, plain, (![A_13, C_15, B_14, D_16]: (r2_hidden(A_13, C_15) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.69/1.69  tff(c_810, plain, (![C_159, A_160, D_156, B_158, C_157]: (r2_hidden('#skF_2'(A_160, B_158, C_157), C_159) | ~r2_hidden(A_160, k2_zfmisc_1(C_159, D_156)) | ~r2_hidden(A_160, k2_zfmisc_1(B_158, C_157)))), inference(superposition, [status(thm), theory('equality')], [c_230, c_16])).
% 3.69/1.69  tff(c_863, plain, (![B_162, C_163]: (r2_hidden('#skF_2'('#skF_7', B_162, C_163), '#skF_4') | ~r2_hidden('#skF_7', k2_zfmisc_1(B_162, C_163)))), inference(resolution, [status(thm)], [c_161, c_810])).
% 3.69/1.69  tff(c_18, plain, (![B_18, A_17]: (m1_subset_1(B_18, A_17) | ~r2_hidden(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.69/1.69  tff(c_868, plain, (![B_162, C_163]: (m1_subset_1('#skF_2'('#skF_7', B_162, C_163), '#skF_4') | v1_xboole_0('#skF_4') | ~r2_hidden('#skF_7', k2_zfmisc_1(B_162, C_163)))), inference(resolution, [status(thm)], [c_863, c_18])).
% 3.69/1.69  tff(c_877, plain, (![B_164, C_165]: (m1_subset_1('#skF_2'('#skF_7', B_164, C_165), '#skF_4') | ~r2_hidden('#skF_7', k2_zfmisc_1(B_164, C_165)))), inference(negUnitSimplification, [status(thm)], [c_420, c_868])).
% 3.69/1.69  tff(c_881, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_4', '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_288, c_877])).
% 3.69/1.69  tff(c_893, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_881])).
% 3.69/1.69  tff(c_895, plain, $false, inference(negUnitSimplification, [status(thm)], [c_415, c_893])).
% 3.69/1.69  tff(c_897, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_419])).
% 3.69/1.69  tff(c_1202, plain, (![D_204, B_206, C_207, C_205, A_208]: (r2_hidden('#skF_2'(A_208, B_206, C_205), C_207) | ~r2_hidden(A_208, k2_zfmisc_1(C_207, D_204)) | ~r2_hidden(A_208, k2_zfmisc_1(B_206, C_205)))), inference(superposition, [status(thm), theory('equality')], [c_230, c_16])).
% 3.69/1.69  tff(c_1239, plain, (![B_209, C_210]: (r2_hidden('#skF_2'('#skF_7', B_209, C_210), '#skF_4') | ~r2_hidden('#skF_7', k2_zfmisc_1(B_209, C_210)))), inference(resolution, [status(thm)], [c_161, c_1202])).
% 3.69/1.69  tff(c_8, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.69/1.69  tff(c_1247, plain, (![B_209, C_210]: (~v1_xboole_0('#skF_4') | ~r2_hidden('#skF_7', k2_zfmisc_1(B_209, C_210)))), inference(resolution, [status(thm)], [c_1239, c_8])).
% 3.69/1.69  tff(c_1253, plain, (![B_209, C_210]: (~r2_hidden('#skF_7', k2_zfmisc_1(B_209, C_210)))), inference(demodulation, [status(thm), theory('equality')], [c_897, c_1247])).
% 3.69/1.69  tff(c_1255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1253, c_161])).
% 3.69/1.69  tff(c_1256, plain, (~m1_subset_1('#skF_3'('#skF_7', '#skF_4', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_399])).
% 3.69/1.69  tff(c_1261, plain, (~v1_xboole_0('#skF_3'('#skF_7', '#skF_4', '#skF_5')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_22, c_1256])).
% 3.69/1.69  tff(c_1266, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1261])).
% 3.69/1.69  tff(c_14, plain, (![B_14, D_16, A_13, C_15]: (r2_hidden(B_14, D_16) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.69/1.69  tff(c_1424, plain, (![C_230, A_233, B_231, C_232, D_229]: (r2_hidden('#skF_3'(A_233, B_231, C_230), D_229) | ~r2_hidden(A_233, k2_zfmisc_1(C_232, D_229)) | ~r2_hidden(A_233, k2_zfmisc_1(B_231, C_230)))), inference(superposition, [status(thm), theory('equality')], [c_230, c_14])).
% 3.69/1.69  tff(c_1453, plain, (![B_234, C_235]: (r2_hidden('#skF_3'('#skF_7', B_234, C_235), '#skF_5') | ~r2_hidden('#skF_7', k2_zfmisc_1(B_234, C_235)))), inference(resolution, [status(thm)], [c_161, c_1424])).
% 3.69/1.69  tff(c_1458, plain, (![B_234, C_235]: (m1_subset_1('#skF_3'('#skF_7', B_234, C_235), '#skF_5') | v1_xboole_0('#skF_5') | ~r2_hidden('#skF_7', k2_zfmisc_1(B_234, C_235)))), inference(resolution, [status(thm)], [c_1453, c_18])).
% 3.69/1.69  tff(c_1467, plain, (![B_236, C_237]: (m1_subset_1('#skF_3'('#skF_7', B_236, C_237), '#skF_5') | ~r2_hidden('#skF_7', k2_zfmisc_1(B_236, C_237)))), inference(negUnitSimplification, [status(thm)], [c_1266, c_1458])).
% 3.69/1.69  tff(c_1471, plain, (m1_subset_1('#skF_3'('#skF_7', '#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_288, c_1467])).
% 3.69/1.69  tff(c_1483, plain, (m1_subset_1('#skF_3'('#skF_7', '#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1471])).
% 3.69/1.69  tff(c_1485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1256, c_1483])).
% 3.69/1.69  tff(c_1487, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1261])).
% 3.69/1.69  tff(c_10, plain, (![A_8, B_9, C_10]: (k4_tarski('#skF_2'(A_8, B_9, C_10), '#skF_3'(A_8, B_9, C_10))=A_8 | ~r2_hidden(A_8, k2_zfmisc_1(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.69/1.69  tff(c_289, plain, (![B_85]: (r2_hidden(B_85, k2_zfmisc_1('#skF_4', '#skF_5')) | ~m1_subset_1(B_85, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_35, c_283])).
% 3.69/1.69  tff(c_318, plain, (![B_86, A_87]: (r2_hidden(B_86, '#skF_5') | ~m1_subset_1(k4_tarski(A_87, B_86), '#skF_6'))), inference(resolution, [status(thm)], [c_289, c_14])).
% 3.69/1.69  tff(c_1672, plain, (![A_259, B_260, C_261]: (r2_hidden('#skF_3'(A_259, B_260, C_261), '#skF_5') | ~m1_subset_1(A_259, '#skF_6') | ~r2_hidden(A_259, k2_zfmisc_1(B_260, C_261)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_318])).
% 3.69/1.69  tff(c_1680, plain, (![A_259, B_260, C_261]: (~v1_xboole_0('#skF_5') | ~m1_subset_1(A_259, '#skF_6') | ~r2_hidden(A_259, k2_zfmisc_1(B_260, C_261)))), inference(resolution, [status(thm)], [c_1672, c_8])).
% 3.69/1.69  tff(c_1687, plain, (![A_262, B_263, C_264]: (~m1_subset_1(A_262, '#skF_6') | ~r2_hidden(A_262, k2_zfmisc_1(B_263, C_264)))), inference(demodulation, [status(thm), theory('equality')], [c_1487, c_1680])).
% 3.69/1.69  tff(c_1703, plain, (~m1_subset_1('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_161, c_1687])).
% 3.69/1.69  tff(c_1723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1703])).
% 3.69/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.69  
% 3.69/1.69  Inference rules
% 3.69/1.69  ----------------------
% 3.69/1.69  #Ref     : 0
% 3.69/1.69  #Sup     : 366
% 3.69/1.69  #Fact    : 0
% 3.69/1.69  #Define  : 0
% 3.69/1.69  #Split   : 14
% 3.69/1.69  #Chain   : 0
% 3.69/1.69  #Close   : 0
% 3.69/1.69  
% 3.69/1.69  Ordering : KBO
% 3.69/1.69  
% 3.69/1.69  Simplification rules
% 3.69/1.69  ----------------------
% 3.69/1.69  #Subsume      : 129
% 3.69/1.69  #Demod        : 64
% 3.69/1.69  #Tautology    : 56
% 3.69/1.69  #SimpNegUnit  : 56
% 3.69/1.69  #BackRed      : 2
% 3.69/1.69  
% 3.69/1.69  #Partial instantiations: 0
% 3.69/1.69  #Strategies tried      : 1
% 3.69/1.69  
% 3.69/1.69  Timing (in seconds)
% 3.69/1.69  ----------------------
% 3.97/1.69  Preprocessing        : 0.30
% 3.97/1.69  Parsing              : 0.16
% 3.97/1.69  CNF conversion       : 0.02
% 3.97/1.69  Main loop            : 0.54
% 3.97/1.69  Inferencing          : 0.21
% 3.97/1.69  Reduction            : 0.14
% 3.97/1.69  Demodulation         : 0.09
% 3.97/1.69  BG Simplification    : 0.03
% 3.97/1.69  Subsumption          : 0.12
% 3.97/1.69  Abstraction          : 0.02
% 3.97/1.69  MUC search           : 0.00
% 3.97/1.69  Cooper               : 0.00
% 3.97/1.69  Total                : 0.88
% 3.97/1.69  Index Insertion      : 0.00
% 3.97/1.69  Index Deletion       : 0.00
% 3.97/1.69  Index Matching       : 0.00
% 3.97/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
