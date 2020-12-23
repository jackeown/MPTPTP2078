%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:19 EST 2020

% Result     : Theorem 18.69s
% Output     : CNFRefutation 18.90s
% Verified   : 
% Statistics : Number of formulae       :  177 (1440 expanded)
%              Number of leaves         :   30 ( 483 expanded)
%              Depth                    :   22
%              Number of atoms          :  324 (3670 expanded)
%              Number of equality atoms :  161 (1892 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_8 > #skF_3 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_99,negated_conjecture,(
    ~ ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(c_88,plain,(
    ! [A_52] : k2_tarski(A_52,A_52) = k1_tarski(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [D_8,A_3] : r2_hidden(D_8,k2_tarski(A_3,D_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_94,plain,(
    ! [A_52] : r2_hidden(A_52,k1_tarski(A_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_10])).

tff(c_76,plain,(
    k1_setfam_1(k1_tarski('#skF_8')) != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12,plain,(
    ! [D_8,B_4] : r2_hidden(D_8,k2_tarski(D_8,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_70,plain,(
    ! [B_42,A_41] :
      ( r1_tarski(k1_setfam_1(B_42),A_41)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_187,plain,(
    ! [B_78,A_79] :
      ( k1_tarski(B_78) = A_79
      | k1_xboole_0 = A_79
      | ~ r1_tarski(A_79,k1_tarski(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_270,plain,(
    ! [B_90,B_91] :
      ( k1_tarski(B_90) = k1_setfam_1(B_91)
      | k1_setfam_1(B_91) = k1_xboole_0
      | ~ r2_hidden(k1_tarski(B_90),B_91) ) ),
    inference(resolution,[status(thm)],[c_70,c_187])).

tff(c_289,plain,(
    ! [A_3,B_90] :
      ( k1_setfam_1(k2_tarski(A_3,k1_tarski(B_90))) = k1_tarski(B_90)
      | k1_setfam_1(k2_tarski(A_3,k1_tarski(B_90))) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_270])).

tff(c_616,plain,(
    ! [A_125,B_126] :
      ( k1_setfam_1(k2_tarski(A_125,k1_tarski(B_126))) = k1_xboole_0
      | k1_tarski(B_126) != k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_289])).

tff(c_664,plain,(
    ! [A_127,A_128,B_129] :
      ( r1_tarski(k1_xboole_0,A_127)
      | ~ r2_hidden(A_127,k2_tarski(A_128,k1_tarski(B_129)))
      | k1_tarski(B_129) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_70])).

tff(c_689,plain,(
    ! [D_8,B_129] :
      ( r1_tarski(k1_xboole_0,D_8)
      | k1_tarski(B_129) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_664])).

tff(c_696,plain,(
    ! [B_129] : k1_tarski(B_129) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_689])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_235,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_7'(A_86,B_87),A_86)
      | r1_tarski(B_87,k1_setfam_1(A_86))
      | k1_xboole_0 = A_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_135,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(k1_tarski(A_64),k1_tarski(B_65)) = k1_tarski(A_64)
      | B_65 = A_64 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [C_21,B_20] : ~ r2_hidden(C_21,k4_xboole_0(B_20,k1_tarski(C_21))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_145,plain,(
    ! [B_65,A_64] :
      ( ~ r2_hidden(B_65,k1_tarski(A_64))
      | B_65 = A_64 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_44])).

tff(c_261,plain,(
    ! [A_64,B_87] :
      ( '#skF_7'(k1_tarski(A_64),B_87) = A_64
      | r1_tarski(B_87,k1_setfam_1(k1_tarski(A_64)))
      | k1_tarski(A_64) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_235,c_145])).

tff(c_716,plain,(
    ! [A_137,B_138] :
      ( '#skF_7'(k1_tarski(A_137),B_138) = A_137
      | r1_tarski(B_138,k1_setfam_1(k1_tarski(A_137))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_696,c_261])).

tff(c_121,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [B_42,A_41] :
      ( k1_setfam_1(B_42) = A_41
      | ~ r1_tarski(A_41,k1_setfam_1(B_42))
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_70,c_121])).

tff(c_826,plain,(
    ! [A_143,B_144] :
      ( k1_setfam_1(k1_tarski(A_143)) = B_144
      | ~ r2_hidden(B_144,k1_tarski(A_143))
      | '#skF_7'(k1_tarski(A_143),B_144) = A_143 ) ),
    inference(resolution,[status(thm)],[c_716,c_128])).

tff(c_850,plain,(
    ! [A_145] :
      ( k1_setfam_1(k1_tarski(A_145)) = A_145
      | '#skF_7'(k1_tarski(A_145),A_145) = A_145 ) ),
    inference(resolution,[status(thm)],[c_94,c_826])).

tff(c_915,plain,(
    '#skF_7'(k1_tarski('#skF_8'),'#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_850,c_76])).

tff(c_72,plain,(
    ! [B_44,A_43] :
      ( ~ r1_tarski(B_44,'#skF_7'(A_43,B_44))
      | r1_tarski(B_44,k1_setfam_1(A_43))
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_928,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | r1_tarski('#skF_8',k1_setfam_1(k1_tarski('#skF_8')))
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_72])).

tff(c_936,plain,
    ( r1_tarski('#skF_8',k1_setfam_1(k1_tarski('#skF_8')))
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_928])).

tff(c_937,plain,(
    r1_tarski('#skF_8',k1_setfam_1(k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_696,c_936])).

tff(c_943,plain,
    ( k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8'
    | ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_937,c_128])).

tff(c_951,plain,(
    k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_943])).

tff(c_953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_951])).

tff(c_960,plain,(
    ! [D_146] : r1_tarski(k1_xboole_0,D_146) ),
    inference(splitRight,[status(thm)],[c_689])).

tff(c_998,plain,(
    ! [B_148] :
      ( k1_setfam_1(B_148) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,B_148) ) ),
    inference(resolution,[status(thm)],[c_960,c_128])).

tff(c_1016,plain,(
    k1_setfam_1(k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_94,c_998])).

tff(c_68,plain,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_204,plain,(
    ! [B_80,A_81] :
      ( k1_setfam_1(B_80) = A_81
      | ~ r1_tarski(A_81,k1_setfam_1(B_80))
      | ~ r2_hidden(A_81,B_80) ) ),
    inference(resolution,[status(thm)],[c_70,c_121])).

tff(c_371,plain,(
    ! [B_102,B_101] :
      ( k1_setfam_1(B_102) = k1_setfam_1(B_101)
      | ~ r2_hidden(k1_setfam_1(B_102),B_101)
      | ~ r2_hidden(k1_setfam_1(B_101),B_102) ) ),
    inference(resolution,[status(thm)],[c_70,c_204])).

tff(c_418,plain,(
    ! [B_106] :
      ( k1_setfam_1(k1_tarski(k1_setfam_1(B_106))) = k1_setfam_1(B_106)
      | ~ r2_hidden(k1_setfam_1(k1_tarski(k1_setfam_1(B_106))),B_106) ) ),
    inference(resolution,[status(thm)],[c_94,c_371])).

tff(c_431,plain,
    ( k1_setfam_1(k1_tarski(k1_setfam_1(k1_xboole_0))) = k1_setfam_1(k1_xboole_0)
    | ~ r2_hidden(k1_setfam_1(k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_418])).

tff(c_433,plain,
    ( k1_setfam_1(k1_tarski(k1_xboole_0)) = k1_xboole_0
    | ~ r2_hidden(k1_setfam_1(k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_431])).

tff(c_434,plain,(
    ~ r2_hidden(k1_setfam_1(k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_433])).

tff(c_1019,plain,(
    ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_434])).

tff(c_1824,plain,(
    ! [A_186,B_187,D_188] :
      ( r2_hidden('#skF_4'(A_186,B_187),D_188)
      | ~ r2_hidden(D_188,A_186)
      | r2_hidden('#skF_6'(A_186,B_187),A_186)
      | k1_setfam_1(A_186) = B_187
      | k1_xboole_0 = A_186 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_52,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden('#skF_4'(A_22,B_23),B_23)
      | r2_hidden('#skF_6'(A_22,B_23),A_22)
      | k1_setfam_1(A_22) = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1941,plain,(
    ! [D_189,A_190] :
      ( ~ r2_hidden(D_189,A_190)
      | r2_hidden('#skF_6'(A_190,D_189),A_190)
      | k1_setfam_1(A_190) = D_189
      | k1_xboole_0 = A_190 ) ),
    inference(resolution,[status(thm)],[c_1824,c_52])).

tff(c_7896,plain,(
    ! [A_9757,D_9758] :
      ( '#skF_6'(k1_tarski(A_9757),D_9758) = A_9757
      | ~ r2_hidden(D_9758,k1_tarski(A_9757))
      | k1_setfam_1(k1_tarski(A_9757)) = D_9758
      | k1_tarski(A_9757) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1941,c_145])).

tff(c_8009,plain,(
    ! [A_9849] :
      ( '#skF_6'(k1_tarski(A_9849),A_9849) = A_9849
      | k1_setfam_1(k1_tarski(A_9849)) = A_9849
      | k1_tarski(A_9849) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_94,c_7896])).

tff(c_8202,plain,
    ( '#skF_6'(k1_tarski('#skF_8'),'#skF_8') = '#skF_8'
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8009,c_76])).

tff(c_8208,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8202])).

tff(c_8489,plain,(
    r2_hidden('#skF_8',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8208,c_94])).

tff(c_1156,plain,(
    ! [A_152] : k1_setfam_1(k2_tarski(A_152,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_998])).

tff(c_310,plain,(
    ! [C_93,D_94,A_95] :
      ( r2_hidden(C_93,D_94)
      | ~ r2_hidden(D_94,A_95)
      | ~ r2_hidden(C_93,k1_setfam_1(A_95))
      | k1_xboole_0 = A_95 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_325,plain,(
    ! [C_93,D_8,B_4] :
      ( r2_hidden(C_93,D_8)
      | ~ r2_hidden(C_93,k1_setfam_1(k2_tarski(D_8,B_4)))
      | k2_tarski(D_8,B_4) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_310])).

tff(c_1167,plain,(
    ! [C_93,A_152] :
      ( r2_hidden(C_93,A_152)
      | ~ r2_hidden(C_93,k1_xboole_0)
      | k2_tarski(A_152,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1156,c_325])).

tff(c_8731,plain,(
    ! [A_10666] :
      ( r2_hidden('#skF_8',A_10666)
      | k2_tarski(A_10666,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8489,c_1167])).

tff(c_8486,plain,(
    ! [B_20] : ~ r2_hidden('#skF_8',k4_xboole_0(B_20,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8208,c_44])).

tff(c_8887,plain,(
    ! [B_10757] : k2_tarski(k4_xboole_0(B_10757,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8731,c_8486])).

tff(c_8912,plain,(
    r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8887,c_10])).

tff(c_9002,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1019,c_8912])).

tff(c_9004,plain,(
    k1_tarski('#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8202])).

tff(c_58,plain,(
    ! [A_22,B_23,D_39] :
      ( r2_hidden('#skF_4'(A_22,B_23),D_39)
      | ~ r2_hidden(D_39,A_22)
      | r2_hidden('#skF_5'(A_22,B_23),B_23)
      | k1_setfam_1(A_22) = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_9003,plain,(
    '#skF_6'(k1_tarski('#skF_8'),'#skF_8') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_8202])).

tff(c_48,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden('#skF_4'(A_22,B_23),B_23)
      | ~ r2_hidden('#skF_5'(A_22,B_23),'#skF_6'(A_22,B_23))
      | k1_setfam_1(A_22) = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_9021,plain,
    ( ~ r2_hidden('#skF_4'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8')
    | ~ r2_hidden('#skF_5'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8')
    | k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8'
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9003,c_48])).

tff(c_9067,plain,
    ( ~ r2_hidden('#skF_4'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8')
    | ~ r2_hidden('#skF_5'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_9004,c_76,c_9021])).

tff(c_9143,plain,(
    ~ r2_hidden('#skF_5'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_9067])).

tff(c_9154,plain,(
    ! [D_39] :
      ( r2_hidden('#skF_4'(k1_tarski('#skF_8'),'#skF_8'),D_39)
      | ~ r2_hidden(D_39,k1_tarski('#skF_8'))
      | k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8'
      | k1_tarski('#skF_8') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_58,c_9143])).

tff(c_9174,plain,(
    ! [D_11299] :
      ( r2_hidden('#skF_4'(k1_tarski('#skF_8'),'#skF_8'),D_11299)
      | ~ r2_hidden(D_11299,k1_tarski('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9004,c_76,c_9154])).

tff(c_56,plain,(
    ! [A_22,B_23] :
      ( ~ r2_hidden('#skF_4'(A_22,B_23),B_23)
      | r2_hidden('#skF_5'(A_22,B_23),B_23)
      | k1_setfam_1(A_22) = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_9157,plain,
    ( ~ r2_hidden('#skF_4'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8')
    | k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8'
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_9143])).

tff(c_9163,plain,(
    ~ r2_hidden('#skF_4'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_9004,c_76,c_9157])).

tff(c_9177,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_9174,c_9163])).

tff(c_9297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_9177])).

tff(c_9299,plain,(
    r2_hidden('#skF_5'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_9067])).

tff(c_50,plain,(
    ! [A_22,B_23,D_39] :
      ( r2_hidden('#skF_4'(A_22,B_23),D_39)
      | ~ r2_hidden(D_39,A_22)
      | ~ r2_hidden('#skF_5'(A_22,B_23),'#skF_6'(A_22,B_23))
      | k1_setfam_1(A_22) = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_9012,plain,(
    ! [D_39] :
      ( r2_hidden('#skF_4'(k1_tarski('#skF_8'),'#skF_8'),D_39)
      | ~ r2_hidden(D_39,k1_tarski('#skF_8'))
      | ~ r2_hidden('#skF_5'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8')
      | k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8'
      | k1_tarski('#skF_8') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9003,c_50])).

tff(c_9061,plain,(
    ! [D_39] :
      ( r2_hidden('#skF_4'(k1_tarski('#skF_8'),'#skF_8'),D_39)
      | ~ r2_hidden(D_39,k1_tarski('#skF_8'))
      | ~ r2_hidden('#skF_5'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_9004,c_76,c_9012])).

tff(c_9668,plain,(
    ! [D_11753] :
      ( r2_hidden('#skF_4'(k1_tarski('#skF_8'),'#skF_8'),D_11753)
      | ~ r2_hidden(D_11753,k1_tarski('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9299,c_9061])).

tff(c_9298,plain,(
    ~ r2_hidden('#skF_4'(k1_tarski('#skF_8'),'#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_9067])).

tff(c_9671,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_9668,c_9298])).

tff(c_9791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_9671])).

tff(c_9792,plain,(
    k1_setfam_1(k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_9793,plain,(
    r2_hidden(k1_setfam_1(k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_9825,plain,(
    r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9792,c_9793])).

tff(c_74,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_7'(A_43,B_44),A_43)
      | r1_tarski(B_44,k1_setfam_1(A_43))
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_9843,plain,(
    ! [A_11844] :
      ( r1_tarski(k1_xboole_0,A_11844)
      | ~ r2_hidden(A_11844,k1_tarski(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9792,c_70])).

tff(c_9847,plain,(
    ! [B_44] :
      ( r1_tarski(k1_xboole_0,'#skF_7'(k1_tarski(k1_xboole_0),B_44))
      | r1_tarski(B_44,k1_setfam_1(k1_tarski(k1_xboole_0)))
      | k1_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74,c_9843])).

tff(c_9853,plain,(
    ! [B_44] :
      ( r1_tarski(k1_xboole_0,'#skF_7'(k1_tarski(k1_xboole_0),B_44))
      | r1_tarski(B_44,k1_xboole_0)
      | k1_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9792,c_9847])).

tff(c_9856,plain,(
    k1_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_9853])).

tff(c_32,plain,(
    ! [B_16,A_15] :
      ( k1_tarski(B_16) = A_15
      | k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k1_tarski(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_9881,plain,(
    ! [A_15] :
      ( k1_tarski(k1_xboole_0) = A_15
      | k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9856,c_32])).

tff(c_10009,plain,(
    ! [A_11852] :
      ( k1_xboole_0 = A_11852
      | k1_xboole_0 = A_11852
      | ~ r1_tarski(A_11852,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9856,c_9881])).

tff(c_10021,plain,(
    ! [B_11853] :
      ( k1_setfam_1(B_11853) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,B_11853) ) ),
    inference(resolution,[status(thm)],[c_70,c_10009])).

tff(c_10047,plain,(
    ! [B_4] : k1_setfam_1(k2_tarski(k1_xboole_0,B_4)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_10021])).

tff(c_10445,plain,(
    ! [C_11880,D_11881,A_11882] :
      ( r2_hidden(C_11880,D_11881)
      | ~ r2_hidden(C_11880,k1_setfam_1(k2_tarski(A_11882,D_11881)))
      | k2_tarski(A_11882,D_11881) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_310])).

tff(c_10471,plain,(
    ! [C_11883,B_11884] :
      ( r2_hidden(C_11883,B_11884)
      | ~ r2_hidden(C_11883,k1_xboole_0)
      | k2_tarski(k1_xboole_0,B_11884) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10047,c_10445])).

tff(c_10491,plain,(
    ! [B_11885] :
      ( r2_hidden(k1_xboole_0,B_11885)
      | k2_tarski(k1_xboole_0,B_11885) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9825,c_10471])).

tff(c_9904,plain,(
    ! [B_20] : ~ r2_hidden(k1_xboole_0,k4_xboole_0(B_20,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9856,c_44])).

tff(c_10557,plain,(
    ! [B_11888] : k2_tarski(k1_xboole_0,k4_xboole_0(B_11888,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10491,c_9904])).

tff(c_10583,plain,(
    ! [B_11889] : r2_hidden(k4_xboole_0(B_11889,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10557,c_10])).

tff(c_9889,plain,(
    ! [B_65] :
      ( ~ r2_hidden(B_65,k1_xboole_0)
      | k1_xboole_0 = B_65 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9856,c_145])).

tff(c_10594,plain,(
    ! [B_11889] : k4_xboole_0(B_11889,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10583,c_9889])).

tff(c_10603,plain,(
    ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10594,c_9904])).

tff(c_10609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9825,c_10603])).

tff(c_10611,plain,(
    k1_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_9853])).

tff(c_26,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_290,plain,(
    ! [B_90,B_4] :
      ( k1_setfam_1(k2_tarski(k1_tarski(B_90),B_4)) = k1_tarski(B_90)
      | k1_setfam_1(k2_tarski(k1_tarski(B_90),B_4)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_270])).

tff(c_10865,plain,(
    ! [B_11910,B_11911] :
      ( k1_setfam_1(k2_tarski(k1_tarski(B_11910),B_11911)) = k1_xboole_0
      | k1_tarski(B_11910) != k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_290])).

tff(c_10916,plain,(
    ! [A_11912,B_11913,B_11914] :
      ( r1_tarski(k1_xboole_0,A_11912)
      | ~ r2_hidden(A_11912,k2_tarski(k1_tarski(B_11913),B_11914))
      | k1_tarski(B_11913) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10865,c_70])).

tff(c_10944,plain,(
    ! [D_8,B_11913] :
      ( r1_tarski(k1_xboole_0,D_8)
      | k1_tarski(B_11913) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_10916])).

tff(c_10947,plain,(
    ! [B_11913] : k1_tarski(B_11913) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10944])).

tff(c_10980,plain,(
    ! [A_11921,B_11922] :
      ( '#skF_7'(k1_tarski(A_11921),B_11922) = A_11921
      | r1_tarski(B_11922,k1_setfam_1(k1_tarski(A_11921))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10947,c_261])).

tff(c_11097,plain,(
    ! [A_11929,B_11930] :
      ( k1_setfam_1(k1_tarski(A_11929)) = B_11930
      | ~ r2_hidden(B_11930,k1_tarski(A_11929))
      | '#skF_7'(k1_tarski(A_11929),B_11930) = A_11929 ) ),
    inference(resolution,[status(thm)],[c_10980,c_128])).

tff(c_11121,plain,(
    ! [A_11931] :
      ( k1_setfam_1(k1_tarski(A_11931)) = A_11931
      | '#skF_7'(k1_tarski(A_11931),A_11931) = A_11931 ) ),
    inference(resolution,[status(thm)],[c_94,c_11097])).

tff(c_11197,plain,(
    '#skF_7'(k1_tarski('#skF_8'),'#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_11121,c_76])).

tff(c_11211,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | r1_tarski('#skF_8',k1_setfam_1(k1_tarski('#skF_8')))
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11197,c_72])).

tff(c_11219,plain,
    ( r1_tarski('#skF_8',k1_setfam_1(k1_tarski('#skF_8')))
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11211])).

tff(c_11220,plain,(
    r1_tarski('#skF_8',k1_setfam_1(k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_10947,c_11219])).

tff(c_11226,plain,
    ( k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8'
    | ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_11220,c_128])).

tff(c_11234,plain,(
    k1_setfam_1(k1_tarski('#skF_8')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_11226])).

tff(c_11236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_11234])).

tff(c_11251,plain,(
    ! [D_11934] : r1_tarski(k1_xboole_0,D_11934) ),
    inference(splitRight,[status(thm)],[c_10944])).

tff(c_11289,plain,(
    ! [B_11936] :
      ( k1_setfam_1(B_11936) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,B_11936) ) ),
    inference(resolution,[status(thm)],[c_11251,c_128])).

tff(c_11322,plain,(
    ! [A_11940] : k1_setfam_1(k2_tarski(A_11940,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_11289])).

tff(c_11440,plain,(
    ! [C_11942,A_11943] :
      ( r2_hidden(C_11942,A_11943)
      | ~ r2_hidden(C_11942,k1_xboole_0)
      | k2_tarski(A_11943,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11322,c_325])).

tff(c_11460,plain,(
    ! [A_11944] :
      ( r2_hidden(k1_xboole_0,A_11944)
      | k2_tarski(A_11944,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9825,c_11440])).

tff(c_11634,plain,(
    ! [B_11950] : k2_tarski(k4_xboole_0(B_11950,k1_tarski(k1_xboole_0)),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11460,c_44])).

tff(c_11675,plain,(
    ! [B_11953] : r2_hidden(k4_xboole_0(B_11953,k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11634,c_12])).

tff(c_11340,plain,(
    ! [C_93,A_11940] :
      ( r2_hidden(C_93,A_11940)
      | ~ r2_hidden(C_93,k1_xboole_0)
      | k2_tarski(A_11940,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11322,c_325])).

tff(c_72285,plain,(
    ! [B_40607,A_40608] :
      ( r2_hidden(k4_xboole_0(B_40607,k1_tarski(k1_xboole_0)),A_40608)
      | k2_tarski(A_40608,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_11675,c_11340])).

tff(c_77742,plain,(
    ! [B_43592] :
      ( k4_xboole_0(B_43592,k1_tarski(k1_xboole_0)) = k1_xboole_0
      | k2_tarski(k1_tarski(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_72285,c_145])).

tff(c_11386,plain,(
    ! [B_11941] : k1_setfam_1(k2_tarski(k1_xboole_0,B_11941)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_11289])).

tff(c_324,plain,(
    ! [C_93,D_8,A_3] :
      ( r2_hidden(C_93,D_8)
      | ~ r2_hidden(C_93,k1_setfam_1(k2_tarski(A_3,D_8)))
      | k2_tarski(A_3,D_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_310])).

tff(c_11796,plain,(
    ! [C_11957,B_11958] :
      ( r2_hidden(C_11957,B_11958)
      | ~ r2_hidden(C_11957,k1_xboole_0)
      | k2_tarski(k1_xboole_0,B_11958) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11386,c_324])).

tff(c_11919,plain,(
    ! [B_11962] :
      ( r2_hidden(k1_xboole_0,B_11962)
      | k2_tarski(k1_xboole_0,B_11962) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9825,c_11796])).

tff(c_11978,plain,(
    ! [B_20] : k2_tarski(k1_xboole_0,k4_xboole_0(B_20,k1_tarski(k1_xboole_0))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11919,c_44])).

tff(c_77744,plain,
    ( k2_tarski(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k2_tarski(k1_tarski(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_77742,c_11978])).

tff(c_79899,plain,
    ( k1_tarski(k1_xboole_0) = k1_xboole_0
    | k2_tarski(k1_tarski(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_77744])).

tff(c_79900,plain,(
    k2_tarski(k1_tarski(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_10611,c_79899])).

tff(c_80035,plain,(
    r2_hidden(k1_tarski(k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_79900,c_12])).

tff(c_8,plain,(
    ! [D_8,B_4,A_3] :
      ( D_8 = B_4
      | D_8 = A_3
      | ~ r2_hidden(D_8,k2_tarski(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_11650,plain,(
    ! [D_8,B_11950] :
      ( k1_xboole_0 = D_8
      | k4_xboole_0(B_11950,k1_tarski(k1_xboole_0)) = D_8
      | ~ r2_hidden(D_8,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11634,c_8])).

tff(c_80827,plain,(
    ! [B_11950] :
      ( k1_tarski(k1_xboole_0) = k1_xboole_0
      | k4_xboole_0(B_11950,k1_tarski(k1_xboole_0)) = k1_tarski(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_80035,c_11650])).

tff(c_82134,plain,(
    ! [B_47705] : k4_xboole_0(B_47705,k1_tarski(k1_xboole_0)) = k1_tarski(k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_10611,c_80827])).

tff(c_38,plain,(
    ! [B_18] : k4_xboole_0(k1_tarski(B_18),k1_tarski(B_18)) != k1_tarski(B_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_82860,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_82134,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.69/8.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.69/8.42  
% 18.69/8.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.69/8.43  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_8 > #skF_3 > #skF_7 > #skF_5 > #skF_4
% 18.69/8.43  
% 18.69/8.43  %Foreground sorts:
% 18.69/8.43  
% 18.69/8.43  
% 18.69/8.43  %Background operators:
% 18.69/8.43  
% 18.69/8.43  
% 18.69/8.43  %Foreground operators:
% 18.69/8.43  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 18.69/8.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 18.69/8.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.69/8.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.69/8.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 18.69/8.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.69/8.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.69/8.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.69/8.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.69/8.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.69/8.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.69/8.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 18.69/8.43  tff('#skF_8', type, '#skF_8': $i).
% 18.69/8.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.69/8.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 18.69/8.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.69/8.43  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 18.69/8.43  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 18.69/8.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 18.69/8.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 18.69/8.43  
% 18.90/8.45  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 18.90/8.45  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 18.90/8.45  tff(f_99, negated_conjecture, ~(![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 18.90/8.45  tff(f_87, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 18.90/8.45  tff(f_52, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 18.90/8.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.90/8.45  tff(f_96, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 18.90/8.45  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 18.90/8.45  tff(f_64, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 18.90/8.45  tff(f_83, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 18.90/8.45  tff(c_88, plain, (![A_52]: (k2_tarski(A_52, A_52)=k1_tarski(A_52))), inference(cnfTransformation, [status(thm)], [f_42])).
% 18.90/8.45  tff(c_10, plain, (![D_8, A_3]: (r2_hidden(D_8, k2_tarski(A_3, D_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 18.90/8.45  tff(c_94, plain, (![A_52]: (r2_hidden(A_52, k1_tarski(A_52)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_10])).
% 18.90/8.45  tff(c_76, plain, (k1_setfam_1(k1_tarski('#skF_8'))!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_99])).
% 18.90/8.45  tff(c_12, plain, (![D_8, B_4]: (r2_hidden(D_8, k2_tarski(D_8, B_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 18.90/8.45  tff(c_70, plain, (![B_42, A_41]: (r1_tarski(k1_setfam_1(B_42), A_41) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.90/8.45  tff(c_187, plain, (![B_78, A_79]: (k1_tarski(B_78)=A_79 | k1_xboole_0=A_79 | ~r1_tarski(A_79, k1_tarski(B_78)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 18.90/8.45  tff(c_270, plain, (![B_90, B_91]: (k1_tarski(B_90)=k1_setfam_1(B_91) | k1_setfam_1(B_91)=k1_xboole_0 | ~r2_hidden(k1_tarski(B_90), B_91))), inference(resolution, [status(thm)], [c_70, c_187])).
% 18.90/8.45  tff(c_289, plain, (![A_3, B_90]: (k1_setfam_1(k2_tarski(A_3, k1_tarski(B_90)))=k1_tarski(B_90) | k1_setfam_1(k2_tarski(A_3, k1_tarski(B_90)))=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_270])).
% 18.90/8.45  tff(c_616, plain, (![A_125, B_126]: (k1_setfam_1(k2_tarski(A_125, k1_tarski(B_126)))=k1_xboole_0 | k1_tarski(B_126)!=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_289])).
% 18.90/8.45  tff(c_664, plain, (![A_127, A_128, B_129]: (r1_tarski(k1_xboole_0, A_127) | ~r2_hidden(A_127, k2_tarski(A_128, k1_tarski(B_129))) | k1_tarski(B_129)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_616, c_70])).
% 18.90/8.45  tff(c_689, plain, (![D_8, B_129]: (r1_tarski(k1_xboole_0, D_8) | k1_tarski(B_129)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_664])).
% 18.90/8.45  tff(c_696, plain, (![B_129]: (k1_tarski(B_129)!=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_689])).
% 18.90/8.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.90/8.45  tff(c_235, plain, (![A_86, B_87]: (r2_hidden('#skF_7'(A_86, B_87), A_86) | r1_tarski(B_87, k1_setfam_1(A_86)) | k1_xboole_0=A_86)), inference(cnfTransformation, [status(thm)], [f_96])).
% 18.90/8.45  tff(c_135, plain, (![A_64, B_65]: (k4_xboole_0(k1_tarski(A_64), k1_tarski(B_65))=k1_tarski(A_64) | B_65=A_64)), inference(cnfTransformation, [status(thm)], [f_57])).
% 18.90/8.45  tff(c_44, plain, (![C_21, B_20]: (~r2_hidden(C_21, k4_xboole_0(B_20, k1_tarski(C_21))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 18.90/8.45  tff(c_145, plain, (![B_65, A_64]: (~r2_hidden(B_65, k1_tarski(A_64)) | B_65=A_64)), inference(superposition, [status(thm), theory('equality')], [c_135, c_44])).
% 18.90/8.45  tff(c_261, plain, (![A_64, B_87]: ('#skF_7'(k1_tarski(A_64), B_87)=A_64 | r1_tarski(B_87, k1_setfam_1(k1_tarski(A_64))) | k1_tarski(A_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_235, c_145])).
% 18.90/8.45  tff(c_716, plain, (![A_137, B_138]: ('#skF_7'(k1_tarski(A_137), B_138)=A_137 | r1_tarski(B_138, k1_setfam_1(k1_tarski(A_137))))), inference(negUnitSimplification, [status(thm)], [c_696, c_261])).
% 18.90/8.45  tff(c_121, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.90/8.45  tff(c_128, plain, (![B_42, A_41]: (k1_setfam_1(B_42)=A_41 | ~r1_tarski(A_41, k1_setfam_1(B_42)) | ~r2_hidden(A_41, B_42))), inference(resolution, [status(thm)], [c_70, c_121])).
% 18.90/8.45  tff(c_826, plain, (![A_143, B_144]: (k1_setfam_1(k1_tarski(A_143))=B_144 | ~r2_hidden(B_144, k1_tarski(A_143)) | '#skF_7'(k1_tarski(A_143), B_144)=A_143)), inference(resolution, [status(thm)], [c_716, c_128])).
% 18.90/8.45  tff(c_850, plain, (![A_145]: (k1_setfam_1(k1_tarski(A_145))=A_145 | '#skF_7'(k1_tarski(A_145), A_145)=A_145)), inference(resolution, [status(thm)], [c_94, c_826])).
% 18.90/8.45  tff(c_915, plain, ('#skF_7'(k1_tarski('#skF_8'), '#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_850, c_76])).
% 18.90/8.45  tff(c_72, plain, (![B_44, A_43]: (~r1_tarski(B_44, '#skF_7'(A_43, B_44)) | r1_tarski(B_44, k1_setfam_1(A_43)) | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_96])).
% 18.90/8.45  tff(c_928, plain, (~r1_tarski('#skF_8', '#skF_8') | r1_tarski('#skF_8', k1_setfam_1(k1_tarski('#skF_8'))) | k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_915, c_72])).
% 18.90/8.45  tff(c_936, plain, (r1_tarski('#skF_8', k1_setfam_1(k1_tarski('#skF_8'))) | k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_928])).
% 18.90/8.45  tff(c_937, plain, (r1_tarski('#skF_8', k1_setfam_1(k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_696, c_936])).
% 18.90/8.45  tff(c_943, plain, (k1_setfam_1(k1_tarski('#skF_8'))='#skF_8' | ~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_937, c_128])).
% 18.90/8.45  tff(c_951, plain, (k1_setfam_1(k1_tarski('#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_943])).
% 18.90/8.45  tff(c_953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_951])).
% 18.90/8.45  tff(c_960, plain, (![D_146]: (r1_tarski(k1_xboole_0, D_146))), inference(splitRight, [status(thm)], [c_689])).
% 18.90/8.45  tff(c_998, plain, (![B_148]: (k1_setfam_1(B_148)=k1_xboole_0 | ~r2_hidden(k1_xboole_0, B_148))), inference(resolution, [status(thm)], [c_960, c_128])).
% 18.90/8.45  tff(c_1016, plain, (k1_setfam_1(k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_94, c_998])).
% 18.90/8.45  tff(c_68, plain, (k1_setfam_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 18.90/8.45  tff(c_204, plain, (![B_80, A_81]: (k1_setfam_1(B_80)=A_81 | ~r1_tarski(A_81, k1_setfam_1(B_80)) | ~r2_hidden(A_81, B_80))), inference(resolution, [status(thm)], [c_70, c_121])).
% 18.90/8.45  tff(c_371, plain, (![B_102, B_101]: (k1_setfam_1(B_102)=k1_setfam_1(B_101) | ~r2_hidden(k1_setfam_1(B_102), B_101) | ~r2_hidden(k1_setfam_1(B_101), B_102))), inference(resolution, [status(thm)], [c_70, c_204])).
% 18.90/8.45  tff(c_418, plain, (![B_106]: (k1_setfam_1(k1_tarski(k1_setfam_1(B_106)))=k1_setfam_1(B_106) | ~r2_hidden(k1_setfam_1(k1_tarski(k1_setfam_1(B_106))), B_106))), inference(resolution, [status(thm)], [c_94, c_371])).
% 18.90/8.45  tff(c_431, plain, (k1_setfam_1(k1_tarski(k1_setfam_1(k1_xboole_0)))=k1_setfam_1(k1_xboole_0) | ~r2_hidden(k1_setfam_1(k1_tarski(k1_xboole_0)), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_68, c_418])).
% 18.90/8.45  tff(c_433, plain, (k1_setfam_1(k1_tarski(k1_xboole_0))=k1_xboole_0 | ~r2_hidden(k1_setfam_1(k1_tarski(k1_xboole_0)), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_431])).
% 18.90/8.45  tff(c_434, plain, (~r2_hidden(k1_setfam_1(k1_tarski(k1_xboole_0)), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_433])).
% 18.90/8.45  tff(c_1019, plain, (~r2_hidden(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1016, c_434])).
% 18.90/8.45  tff(c_1824, plain, (![A_186, B_187, D_188]: (r2_hidden('#skF_4'(A_186, B_187), D_188) | ~r2_hidden(D_188, A_186) | r2_hidden('#skF_6'(A_186, B_187), A_186) | k1_setfam_1(A_186)=B_187 | k1_xboole_0=A_186)), inference(cnfTransformation, [status(thm)], [f_83])).
% 18.90/8.45  tff(c_52, plain, (![A_22, B_23]: (~r2_hidden('#skF_4'(A_22, B_23), B_23) | r2_hidden('#skF_6'(A_22, B_23), A_22) | k1_setfam_1(A_22)=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_83])).
% 18.90/8.45  tff(c_1941, plain, (![D_189, A_190]: (~r2_hidden(D_189, A_190) | r2_hidden('#skF_6'(A_190, D_189), A_190) | k1_setfam_1(A_190)=D_189 | k1_xboole_0=A_190)), inference(resolution, [status(thm)], [c_1824, c_52])).
% 18.90/8.45  tff(c_7896, plain, (![A_9757, D_9758]: ('#skF_6'(k1_tarski(A_9757), D_9758)=A_9757 | ~r2_hidden(D_9758, k1_tarski(A_9757)) | k1_setfam_1(k1_tarski(A_9757))=D_9758 | k1_tarski(A_9757)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1941, c_145])).
% 18.90/8.45  tff(c_8009, plain, (![A_9849]: ('#skF_6'(k1_tarski(A_9849), A_9849)=A_9849 | k1_setfam_1(k1_tarski(A_9849))=A_9849 | k1_tarski(A_9849)=k1_xboole_0)), inference(resolution, [status(thm)], [c_94, c_7896])).
% 18.90/8.45  tff(c_8202, plain, ('#skF_6'(k1_tarski('#skF_8'), '#skF_8')='#skF_8' | k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8009, c_76])).
% 18.90/8.45  tff(c_8208, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8202])).
% 18.90/8.45  tff(c_8489, plain, (r2_hidden('#skF_8', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8208, c_94])).
% 18.90/8.45  tff(c_1156, plain, (![A_152]: (k1_setfam_1(k2_tarski(A_152, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_998])).
% 18.90/8.45  tff(c_310, plain, (![C_93, D_94, A_95]: (r2_hidden(C_93, D_94) | ~r2_hidden(D_94, A_95) | ~r2_hidden(C_93, k1_setfam_1(A_95)) | k1_xboole_0=A_95)), inference(cnfTransformation, [status(thm)], [f_83])).
% 18.90/8.45  tff(c_325, plain, (![C_93, D_8, B_4]: (r2_hidden(C_93, D_8) | ~r2_hidden(C_93, k1_setfam_1(k2_tarski(D_8, B_4))) | k2_tarski(D_8, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_310])).
% 18.90/8.45  tff(c_1167, plain, (![C_93, A_152]: (r2_hidden(C_93, A_152) | ~r2_hidden(C_93, k1_xboole_0) | k2_tarski(A_152, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1156, c_325])).
% 18.90/8.45  tff(c_8731, plain, (![A_10666]: (r2_hidden('#skF_8', A_10666) | k2_tarski(A_10666, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8489, c_1167])).
% 18.90/8.45  tff(c_8486, plain, (![B_20]: (~r2_hidden('#skF_8', k4_xboole_0(B_20, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8208, c_44])).
% 18.90/8.45  tff(c_8887, plain, (![B_10757]: (k2_tarski(k4_xboole_0(B_10757, k1_xboole_0), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8731, c_8486])).
% 18.90/8.45  tff(c_8912, plain, (r2_hidden(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8887, c_10])).
% 18.90/8.45  tff(c_9002, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1019, c_8912])).
% 18.90/8.45  tff(c_9004, plain, (k1_tarski('#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_8202])).
% 18.90/8.45  tff(c_58, plain, (![A_22, B_23, D_39]: (r2_hidden('#skF_4'(A_22, B_23), D_39) | ~r2_hidden(D_39, A_22) | r2_hidden('#skF_5'(A_22, B_23), B_23) | k1_setfam_1(A_22)=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_83])).
% 18.90/8.45  tff(c_9003, plain, ('#skF_6'(k1_tarski('#skF_8'), '#skF_8')='#skF_8'), inference(splitRight, [status(thm)], [c_8202])).
% 18.90/8.45  tff(c_48, plain, (![A_22, B_23]: (~r2_hidden('#skF_4'(A_22, B_23), B_23) | ~r2_hidden('#skF_5'(A_22, B_23), '#skF_6'(A_22, B_23)) | k1_setfam_1(A_22)=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_83])).
% 18.90/8.45  tff(c_9021, plain, (~r2_hidden('#skF_4'(k1_tarski('#skF_8'), '#skF_8'), '#skF_8') | ~r2_hidden('#skF_5'(k1_tarski('#skF_8'), '#skF_8'), '#skF_8') | k1_setfam_1(k1_tarski('#skF_8'))='#skF_8' | k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_9003, c_48])).
% 18.90/8.45  tff(c_9067, plain, (~r2_hidden('#skF_4'(k1_tarski('#skF_8'), '#skF_8'), '#skF_8') | ~r2_hidden('#skF_5'(k1_tarski('#skF_8'), '#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_9004, c_76, c_9021])).
% 18.90/8.45  tff(c_9143, plain, (~r2_hidden('#skF_5'(k1_tarski('#skF_8'), '#skF_8'), '#skF_8')), inference(splitLeft, [status(thm)], [c_9067])).
% 18.90/8.45  tff(c_9154, plain, (![D_39]: (r2_hidden('#skF_4'(k1_tarski('#skF_8'), '#skF_8'), D_39) | ~r2_hidden(D_39, k1_tarski('#skF_8')) | k1_setfam_1(k1_tarski('#skF_8'))='#skF_8' | k1_tarski('#skF_8')=k1_xboole_0)), inference(resolution, [status(thm)], [c_58, c_9143])).
% 18.90/8.45  tff(c_9174, plain, (![D_11299]: (r2_hidden('#skF_4'(k1_tarski('#skF_8'), '#skF_8'), D_11299) | ~r2_hidden(D_11299, k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_9004, c_76, c_9154])).
% 18.90/8.45  tff(c_56, plain, (![A_22, B_23]: (~r2_hidden('#skF_4'(A_22, B_23), B_23) | r2_hidden('#skF_5'(A_22, B_23), B_23) | k1_setfam_1(A_22)=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_83])).
% 18.90/8.45  tff(c_9157, plain, (~r2_hidden('#skF_4'(k1_tarski('#skF_8'), '#skF_8'), '#skF_8') | k1_setfam_1(k1_tarski('#skF_8'))='#skF_8' | k1_tarski('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_9143])).
% 18.90/8.45  tff(c_9163, plain, (~r2_hidden('#skF_4'(k1_tarski('#skF_8'), '#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_9004, c_76, c_9157])).
% 18.90/8.45  tff(c_9177, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_9174, c_9163])).
% 18.90/8.45  tff(c_9297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_9177])).
% 18.90/8.45  tff(c_9299, plain, (r2_hidden('#skF_5'(k1_tarski('#skF_8'), '#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_9067])).
% 18.90/8.45  tff(c_50, plain, (![A_22, B_23, D_39]: (r2_hidden('#skF_4'(A_22, B_23), D_39) | ~r2_hidden(D_39, A_22) | ~r2_hidden('#skF_5'(A_22, B_23), '#skF_6'(A_22, B_23)) | k1_setfam_1(A_22)=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_83])).
% 18.90/8.45  tff(c_9012, plain, (![D_39]: (r2_hidden('#skF_4'(k1_tarski('#skF_8'), '#skF_8'), D_39) | ~r2_hidden(D_39, k1_tarski('#skF_8')) | ~r2_hidden('#skF_5'(k1_tarski('#skF_8'), '#skF_8'), '#skF_8') | k1_setfam_1(k1_tarski('#skF_8'))='#skF_8' | k1_tarski('#skF_8')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9003, c_50])).
% 18.90/8.45  tff(c_9061, plain, (![D_39]: (r2_hidden('#skF_4'(k1_tarski('#skF_8'), '#skF_8'), D_39) | ~r2_hidden(D_39, k1_tarski('#skF_8')) | ~r2_hidden('#skF_5'(k1_tarski('#skF_8'), '#skF_8'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_9004, c_76, c_9012])).
% 18.90/8.45  tff(c_9668, plain, (![D_11753]: (r2_hidden('#skF_4'(k1_tarski('#skF_8'), '#skF_8'), D_11753) | ~r2_hidden(D_11753, k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_9299, c_9061])).
% 18.90/8.45  tff(c_9298, plain, (~r2_hidden('#skF_4'(k1_tarski('#skF_8'), '#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_9067])).
% 18.90/8.45  tff(c_9671, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_9668, c_9298])).
% 18.90/8.45  tff(c_9791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_9671])).
% 18.90/8.45  tff(c_9792, plain, (k1_setfam_1(k1_tarski(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_433])).
% 18.90/8.45  tff(c_9793, plain, (r2_hidden(k1_setfam_1(k1_tarski(k1_xboole_0)), k1_xboole_0)), inference(splitRight, [status(thm)], [c_433])).
% 18.90/8.45  tff(c_9825, plain, (r2_hidden(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_9792, c_9793])).
% 18.90/8.45  tff(c_74, plain, (![A_43, B_44]: (r2_hidden('#skF_7'(A_43, B_44), A_43) | r1_tarski(B_44, k1_setfam_1(A_43)) | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_96])).
% 18.90/8.45  tff(c_9843, plain, (![A_11844]: (r1_tarski(k1_xboole_0, A_11844) | ~r2_hidden(A_11844, k1_tarski(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_9792, c_70])).
% 18.90/8.45  tff(c_9847, plain, (![B_44]: (r1_tarski(k1_xboole_0, '#skF_7'(k1_tarski(k1_xboole_0), B_44)) | r1_tarski(B_44, k1_setfam_1(k1_tarski(k1_xboole_0))) | k1_tarski(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_9843])).
% 18.90/8.45  tff(c_9853, plain, (![B_44]: (r1_tarski(k1_xboole_0, '#skF_7'(k1_tarski(k1_xboole_0), B_44)) | r1_tarski(B_44, k1_xboole_0) | k1_tarski(k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_9792, c_9847])).
% 18.90/8.45  tff(c_9856, plain, (k1_tarski(k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_9853])).
% 18.90/8.45  tff(c_32, plain, (![B_16, A_15]: (k1_tarski(B_16)=A_15 | k1_xboole_0=A_15 | ~r1_tarski(A_15, k1_tarski(B_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 18.90/8.45  tff(c_9881, plain, (![A_15]: (k1_tarski(k1_xboole_0)=A_15 | k1_xboole_0=A_15 | ~r1_tarski(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_9856, c_32])).
% 18.90/8.45  tff(c_10009, plain, (![A_11852]: (k1_xboole_0=A_11852 | k1_xboole_0=A_11852 | ~r1_tarski(A_11852, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_9856, c_9881])).
% 18.90/8.45  tff(c_10021, plain, (![B_11853]: (k1_setfam_1(B_11853)=k1_xboole_0 | ~r2_hidden(k1_xboole_0, B_11853))), inference(resolution, [status(thm)], [c_70, c_10009])).
% 18.90/8.45  tff(c_10047, plain, (![B_4]: (k1_setfam_1(k2_tarski(k1_xboole_0, B_4))=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_10021])).
% 18.90/8.45  tff(c_10445, plain, (![C_11880, D_11881, A_11882]: (r2_hidden(C_11880, D_11881) | ~r2_hidden(C_11880, k1_setfam_1(k2_tarski(A_11882, D_11881))) | k2_tarski(A_11882, D_11881)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_310])).
% 18.90/8.45  tff(c_10471, plain, (![C_11883, B_11884]: (r2_hidden(C_11883, B_11884) | ~r2_hidden(C_11883, k1_xboole_0) | k2_tarski(k1_xboole_0, B_11884)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10047, c_10445])).
% 18.90/8.45  tff(c_10491, plain, (![B_11885]: (r2_hidden(k1_xboole_0, B_11885) | k2_tarski(k1_xboole_0, B_11885)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9825, c_10471])).
% 18.90/8.45  tff(c_9904, plain, (![B_20]: (~r2_hidden(k1_xboole_0, k4_xboole_0(B_20, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_9856, c_44])).
% 18.90/8.45  tff(c_10557, plain, (![B_11888]: (k2_tarski(k1_xboole_0, k4_xboole_0(B_11888, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_10491, c_9904])).
% 18.90/8.45  tff(c_10583, plain, (![B_11889]: (r2_hidden(k4_xboole_0(B_11889, k1_xboole_0), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10557, c_10])).
% 18.90/8.45  tff(c_9889, plain, (![B_65]: (~r2_hidden(B_65, k1_xboole_0) | k1_xboole_0=B_65)), inference(superposition, [status(thm), theory('equality')], [c_9856, c_145])).
% 18.90/8.45  tff(c_10594, plain, (![B_11889]: (k4_xboole_0(B_11889, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10583, c_9889])).
% 18.90/8.45  tff(c_10603, plain, (~r2_hidden(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10594, c_9904])).
% 18.90/8.45  tff(c_10609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9825, c_10603])).
% 18.90/8.45  tff(c_10611, plain, (k1_tarski(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_9853])).
% 18.90/8.45  tff(c_26, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 18.90/8.45  tff(c_290, plain, (![B_90, B_4]: (k1_setfam_1(k2_tarski(k1_tarski(B_90), B_4))=k1_tarski(B_90) | k1_setfam_1(k2_tarski(k1_tarski(B_90), B_4))=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_270])).
% 18.90/8.45  tff(c_10865, plain, (![B_11910, B_11911]: (k1_setfam_1(k2_tarski(k1_tarski(B_11910), B_11911))=k1_xboole_0 | k1_tarski(B_11910)!=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_290])).
% 18.90/8.45  tff(c_10916, plain, (![A_11912, B_11913, B_11914]: (r1_tarski(k1_xboole_0, A_11912) | ~r2_hidden(A_11912, k2_tarski(k1_tarski(B_11913), B_11914)) | k1_tarski(B_11913)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10865, c_70])).
% 18.90/8.45  tff(c_10944, plain, (![D_8, B_11913]: (r1_tarski(k1_xboole_0, D_8) | k1_tarski(B_11913)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_10916])).
% 18.90/8.45  tff(c_10947, plain, (![B_11913]: (k1_tarski(B_11913)!=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_10944])).
% 18.90/8.45  tff(c_10980, plain, (![A_11921, B_11922]: ('#skF_7'(k1_tarski(A_11921), B_11922)=A_11921 | r1_tarski(B_11922, k1_setfam_1(k1_tarski(A_11921))))), inference(negUnitSimplification, [status(thm)], [c_10947, c_261])).
% 18.90/8.45  tff(c_11097, plain, (![A_11929, B_11930]: (k1_setfam_1(k1_tarski(A_11929))=B_11930 | ~r2_hidden(B_11930, k1_tarski(A_11929)) | '#skF_7'(k1_tarski(A_11929), B_11930)=A_11929)), inference(resolution, [status(thm)], [c_10980, c_128])).
% 18.90/8.45  tff(c_11121, plain, (![A_11931]: (k1_setfam_1(k1_tarski(A_11931))=A_11931 | '#skF_7'(k1_tarski(A_11931), A_11931)=A_11931)), inference(resolution, [status(thm)], [c_94, c_11097])).
% 18.90/8.45  tff(c_11197, plain, ('#skF_7'(k1_tarski('#skF_8'), '#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_11121, c_76])).
% 18.90/8.45  tff(c_11211, plain, (~r1_tarski('#skF_8', '#skF_8') | r1_tarski('#skF_8', k1_setfam_1(k1_tarski('#skF_8'))) | k1_tarski('#skF_8')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11197, c_72])).
% 18.90/8.45  tff(c_11219, plain, (r1_tarski('#skF_8', k1_setfam_1(k1_tarski('#skF_8'))) | k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_11211])).
% 18.90/8.45  tff(c_11220, plain, (r1_tarski('#skF_8', k1_setfam_1(k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_10947, c_11219])).
% 18.90/8.45  tff(c_11226, plain, (k1_setfam_1(k1_tarski('#skF_8'))='#skF_8' | ~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_11220, c_128])).
% 18.90/8.45  tff(c_11234, plain, (k1_setfam_1(k1_tarski('#skF_8'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_11226])).
% 18.90/8.45  tff(c_11236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_11234])).
% 18.90/8.45  tff(c_11251, plain, (![D_11934]: (r1_tarski(k1_xboole_0, D_11934))), inference(splitRight, [status(thm)], [c_10944])).
% 18.90/8.45  tff(c_11289, plain, (![B_11936]: (k1_setfam_1(B_11936)=k1_xboole_0 | ~r2_hidden(k1_xboole_0, B_11936))), inference(resolution, [status(thm)], [c_11251, c_128])).
% 18.90/8.45  tff(c_11322, plain, (![A_11940]: (k1_setfam_1(k2_tarski(A_11940, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_11289])).
% 18.90/8.45  tff(c_11440, plain, (![C_11942, A_11943]: (r2_hidden(C_11942, A_11943) | ~r2_hidden(C_11942, k1_xboole_0) | k2_tarski(A_11943, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11322, c_325])).
% 18.90/8.45  tff(c_11460, plain, (![A_11944]: (r2_hidden(k1_xboole_0, A_11944) | k2_tarski(A_11944, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9825, c_11440])).
% 18.90/8.45  tff(c_11634, plain, (![B_11950]: (k2_tarski(k4_xboole_0(B_11950, k1_tarski(k1_xboole_0)), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_11460, c_44])).
% 18.90/8.45  tff(c_11675, plain, (![B_11953]: (r2_hidden(k4_xboole_0(B_11953, k1_tarski(k1_xboole_0)), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11634, c_12])).
% 18.90/8.45  tff(c_11340, plain, (![C_93, A_11940]: (r2_hidden(C_93, A_11940) | ~r2_hidden(C_93, k1_xboole_0) | k2_tarski(A_11940, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11322, c_325])).
% 18.90/8.45  tff(c_72285, plain, (![B_40607, A_40608]: (r2_hidden(k4_xboole_0(B_40607, k1_tarski(k1_xboole_0)), A_40608) | k2_tarski(A_40608, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_11675, c_11340])).
% 18.90/8.45  tff(c_77742, plain, (![B_43592]: (k4_xboole_0(B_43592, k1_tarski(k1_xboole_0))=k1_xboole_0 | k2_tarski(k1_tarski(k1_xboole_0), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_72285, c_145])).
% 18.90/8.45  tff(c_11386, plain, (![B_11941]: (k1_setfam_1(k2_tarski(k1_xboole_0, B_11941))=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_11289])).
% 18.90/8.45  tff(c_324, plain, (![C_93, D_8, A_3]: (r2_hidden(C_93, D_8) | ~r2_hidden(C_93, k1_setfam_1(k2_tarski(A_3, D_8))) | k2_tarski(A_3, D_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_310])).
% 18.90/8.45  tff(c_11796, plain, (![C_11957, B_11958]: (r2_hidden(C_11957, B_11958) | ~r2_hidden(C_11957, k1_xboole_0) | k2_tarski(k1_xboole_0, B_11958)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11386, c_324])).
% 18.90/8.45  tff(c_11919, plain, (![B_11962]: (r2_hidden(k1_xboole_0, B_11962) | k2_tarski(k1_xboole_0, B_11962)=k1_xboole_0)), inference(resolution, [status(thm)], [c_9825, c_11796])).
% 18.90/8.45  tff(c_11978, plain, (![B_20]: (k2_tarski(k1_xboole_0, k4_xboole_0(B_20, k1_tarski(k1_xboole_0)))=k1_xboole_0)), inference(resolution, [status(thm)], [c_11919, c_44])).
% 18.90/8.45  tff(c_77744, plain, (k2_tarski(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | k2_tarski(k1_tarski(k1_xboole_0), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_77742, c_11978])).
% 18.90/8.45  tff(c_79899, plain, (k1_tarski(k1_xboole_0)=k1_xboole_0 | k2_tarski(k1_tarski(k1_xboole_0), k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_77744])).
% 18.90/8.45  tff(c_79900, plain, (k2_tarski(k1_tarski(k1_xboole_0), k1_xboole_0)=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_10611, c_79899])).
% 18.90/8.45  tff(c_80035, plain, (r2_hidden(k1_tarski(k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_79900, c_12])).
% 18.90/8.45  tff(c_8, plain, (![D_8, B_4, A_3]: (D_8=B_4 | D_8=A_3 | ~r2_hidden(D_8, k2_tarski(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 18.90/8.45  tff(c_11650, plain, (![D_8, B_11950]: (k1_xboole_0=D_8 | k4_xboole_0(B_11950, k1_tarski(k1_xboole_0))=D_8 | ~r2_hidden(D_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_11634, c_8])).
% 18.90/8.45  tff(c_80827, plain, (![B_11950]: (k1_tarski(k1_xboole_0)=k1_xboole_0 | k4_xboole_0(B_11950, k1_tarski(k1_xboole_0))=k1_tarski(k1_xboole_0))), inference(resolution, [status(thm)], [c_80035, c_11650])).
% 18.90/8.45  tff(c_82134, plain, (![B_47705]: (k4_xboole_0(B_47705, k1_tarski(k1_xboole_0))=k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_10611, c_80827])).
% 18.90/8.45  tff(c_38, plain, (![B_18]: (k4_xboole_0(k1_tarski(B_18), k1_tarski(B_18))!=k1_tarski(B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 18.90/8.45  tff(c_82860, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_82134, c_38])).
% 18.90/8.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.90/8.45  
% 18.90/8.45  Inference rules
% 18.90/8.45  ----------------------
% 18.90/8.45  #Ref     : 1
% 18.90/8.45  #Sup     : 11249
% 18.90/8.45  #Fact    : 26
% 18.90/8.45  #Define  : 0
% 18.90/8.45  #Split   : 17
% 18.90/8.45  #Chain   : 0
% 18.90/8.45  #Close   : 0
% 18.90/8.45  
% 18.90/8.45  Ordering : KBO
% 18.90/8.45  
% 18.90/8.45  Simplification rules
% 18.90/8.45  ----------------------
% 18.90/8.45  #Subsume      : 2962
% 18.90/8.45  #Demod        : 3026
% 18.90/8.45  #Tautology    : 1866
% 18.90/8.45  #SimpNegUnit  : 226
% 18.90/8.45  #BackRed      : 25
% 18.90/8.45  
% 18.90/8.45  #Partial instantiations: 23715
% 18.90/8.45  #Strategies tried      : 1
% 18.90/8.45  
% 18.90/8.45  Timing (in seconds)
% 18.90/8.45  ----------------------
% 18.90/8.46  Preprocessing        : 0.50
% 18.90/8.46  Parsing              : 0.24
% 18.90/8.46  CNF conversion       : 0.04
% 18.90/8.46  Main loop            : 7.00
% 18.90/8.46  Inferencing          : 2.34
% 18.90/8.46  Reduction            : 1.72
% 18.90/8.46  Demodulation         : 1.18
% 18.90/8.46  BG Simplification    : 0.27
% 18.90/8.46  Subsumption          : 2.35
% 18.90/8.46  Abstraction          : 0.29
% 18.90/8.46  MUC search           : 0.00
% 18.90/8.46  Cooper               : 0.00
% 18.90/8.46  Total                : 7.56
% 18.90/8.46  Index Insertion      : 0.00
% 18.90/8.46  Index Deletion       : 0.00
% 18.90/8.46  Index Matching       : 0.00
% 18.90/8.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
