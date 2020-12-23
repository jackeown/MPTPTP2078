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
% DateTime   : Thu Dec  3 09:54:14 EST 2020

% Result     : Theorem 36.26s
% Output     : CNFRefutation 36.42s
% Verified   : 
% Statistics : Number of formulae       :  257 (2572 expanded)
%              Number of leaves         :   43 ( 876 expanded)
%              Depth                    :   23
%              Number of atoms          :  412 (5311 expanded)
%              Number of equality atoms :  172 (1459 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_14 > #skF_13 > #skF_5 > #skF_10 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_9 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_108,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_106,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_100,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_121,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_104,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_123,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_94,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_100,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_80,plain,(
    ! [C_44] : r2_hidden(C_44,k1_tarski(C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_144,plain,(
    ! [B_58,A_59] :
      ( ~ r2_hidden(B_58,A_59)
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_148,plain,(
    ! [C_44] : ~ v1_xboole_0(k1_tarski(C_44)) ),
    inference(resolution,[status(thm)],[c_80,c_144])).

tff(c_156,plain,(
    ! [A_63] :
      ( v1_xboole_0(A_63)
      | r2_hidden('#skF_1'(A_63),A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [C_44,A_40] :
      ( C_44 = A_40
      | ~ r2_hidden(C_44,k1_tarski(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_160,plain,(
    ! [A_40] :
      ( '#skF_1'(k1_tarski(A_40)) = A_40
      | v1_xboole_0(k1_tarski(A_40)) ) ),
    inference(resolution,[status(thm)],[c_156,c_78])).

tff(c_166,plain,(
    ! [A_40] : '#skF_1'(k1_tarski(A_40)) = A_40 ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_160])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_663,plain,(
    ! [C_128,B_129,A_130] :
      ( r2_hidden(C_128,B_129)
      | ~ r2_hidden(C_128,A_130)
      | ~ r1_tarski(A_130,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_917,plain,(
    ! [A_161,B_162] :
      ( r2_hidden('#skF_1'(A_161),B_162)
      | ~ r1_tarski(A_161,B_162)
      | v1_xboole_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_6,c_663])).

tff(c_76,plain,(
    ! [A_39] : r1_xboole_0(A_39,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_624,plain,(
    ! [A_122,B_123,C_124] :
      ( ~ r1_xboole_0(A_122,B_123)
      | ~ r2_hidden(C_124,B_123)
      | ~ r2_hidden(C_124,A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_633,plain,(
    ! [C_124,A_39] :
      ( ~ r2_hidden(C_124,k1_xboole_0)
      | ~ r2_hidden(C_124,A_39) ) ),
    inference(resolution,[status(thm)],[c_76,c_624])).

tff(c_1298,plain,(
    ! [A_183,A_184] :
      ( ~ r2_hidden('#skF_1'(A_183),A_184)
      | ~ r1_tarski(A_183,k1_xboole_0)
      | v1_xboole_0(A_183) ) ),
    inference(resolution,[status(thm)],[c_917,c_633])).

tff(c_1312,plain,(
    ! [A_40,A_184] :
      ( ~ r2_hidden(A_40,A_184)
      | ~ r1_tarski(k1_tarski(A_40),k1_xboole_0)
      | v1_xboole_0(k1_tarski(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_1298])).

tff(c_1444,plain,(
    ! [A_189,A_190] :
      ( ~ r2_hidden(A_189,A_190)
      | ~ r1_tarski(k1_tarski(A_189),k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_1312])).

tff(c_1477,plain,(
    ! [C_44] : ~ r1_tarski(k1_tarski(C_44),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_80,c_1444])).

tff(c_336,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_2'(A_81,B_82),A_81)
      | r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_350,plain,(
    ! [A_40,B_82] :
      ( '#skF_2'(k1_tarski(A_40),B_82) = A_40
      | r1_tarski(k1_tarski(A_40),B_82) ) ),
    inference(resolution,[status(thm)],[c_336,c_78])).

tff(c_1325,plain,(
    ! [A_185] :
      ( ~ r1_tarski(A_185,k1_xboole_0)
      | v1_xboole_0(A_185) ) ),
    inference(resolution,[status(thm)],[c_6,c_1298])).

tff(c_1329,plain,(
    ! [A_40] :
      ( v1_xboole_0(k1_tarski(A_40))
      | '#skF_2'(k1_tarski(A_40),k1_xboole_0) = A_40 ) ),
    inference(resolution,[status(thm)],[c_350,c_1325])).

tff(c_1406,plain,(
    ! [A_188] : '#skF_2'(k1_tarski(A_188),k1_xboole_0) = A_188 ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_1329])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_2'(A_7,B_8),B_8)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1421,plain,(
    ! [A_188] :
      ( ~ r2_hidden(A_188,k1_xboole_0)
      | r1_tarski(k1_tarski(A_188),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1406,c_10])).

tff(c_1489,plain,(
    ! [A_188] : ~ r2_hidden(A_188,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_1477,c_1421])).

tff(c_74,plain,(
    ! [A_38] : k3_xboole_0(A_38,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1537,plain,(
    ! [A_193,B_194,C_195] :
      ( r2_hidden('#skF_3'(A_193,B_194,C_195),B_194)
      | r2_hidden('#skF_4'(A_193,B_194,C_195),C_195)
      | k3_xboole_0(A_193,B_194) = C_195 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [D_17,B_13,A_12] :
      ( r2_hidden(D_17,B_13)
      | ~ r2_hidden(D_17,k3_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_55301,plain,(
    ! [A_1220,A_1221,B_1222,C_1223] :
      ( r2_hidden('#skF_3'(A_1220,k3_xboole_0(A_1221,B_1222),C_1223),B_1222)
      | r2_hidden('#skF_4'(A_1220,k3_xboole_0(A_1221,B_1222),C_1223),C_1223)
      | k3_xboole_0(A_1220,k3_xboole_0(A_1221,B_1222)) = C_1223 ) ),
    inference(resolution,[status(thm)],[c_1537,c_16])).

tff(c_55655,plain,(
    ! [A_1220,A_38,C_1223] :
      ( r2_hidden('#skF_3'(A_1220,k3_xboole_0(A_38,k1_xboole_0),C_1223),k1_xboole_0)
      | r2_hidden('#skF_4'(A_1220,k1_xboole_0,C_1223),C_1223)
      | k3_xboole_0(A_1220,k3_xboole_0(A_38,k1_xboole_0)) = C_1223 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_55301])).

tff(c_55725,plain,(
    ! [A_1220,C_1223] :
      ( r2_hidden('#skF_3'(A_1220,k1_xboole_0,C_1223),k1_xboole_0)
      | r2_hidden('#skF_4'(A_1220,k1_xboole_0,C_1223),C_1223)
      | k1_xboole_0 = C_1223 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_74,c_55655])).

tff(c_55726,plain,(
    ! [A_1220,C_1223] :
      ( r2_hidden('#skF_4'(A_1220,k1_xboole_0,C_1223),C_1223)
      | k1_xboole_0 = C_1223 ) ),
    inference(negUnitSimplification,[status(thm)],[c_1489,c_55725])).

tff(c_70,plain,(
    ! [B_35] : r1_tarski(B_35,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_98,plain,
    ( '#skF_14' != '#skF_12'
    | '#skF_11' != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_109,plain,(
    '#skF_11' != '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),A_7)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_94,plain,(
    ! [B_46] : k2_zfmisc_1(k1_xboole_0,B_46) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_183,plain,(
    ! [B_67,A_68] : k3_xboole_0(B_67,A_68) = k3_xboole_0(A_68,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_199,plain,(
    ! [A_68] : k3_xboole_0(k1_xboole_0,A_68) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_74])).

tff(c_3558,plain,(
    ! [A_276,B_277,C_278] :
      ( r2_hidden('#skF_3'(A_276,B_277,C_278),A_276)
      | r2_hidden('#skF_4'(A_276,B_277,C_278),C_278)
      | k3_xboole_0(A_276,B_277) = C_278 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [D_17,A_12,B_13] :
      ( r2_hidden(D_17,A_12)
      | ~ r2_hidden(D_17,k3_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52490,plain,(
    ! [A_1187,B_1188,A_1189,B_1190] :
      ( r2_hidden('#skF_4'(A_1187,B_1188,k3_xboole_0(A_1189,B_1190)),A_1189)
      | r2_hidden('#skF_3'(A_1187,B_1188,k3_xboole_0(A_1189,B_1190)),A_1187)
      | k3_xboole_0(A_1189,B_1190) = k3_xboole_0(A_1187,B_1188) ) ),
    inference(resolution,[status(thm)],[c_3558,c_18])).

tff(c_52823,plain,(
    ! [A_1187,B_1188,A_68] :
      ( r2_hidden('#skF_4'(A_1187,B_1188,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_3'(A_1187,B_1188,k3_xboole_0(k1_xboole_0,A_68)),A_1187)
      | k3_xboole_0(k1_xboole_0,A_68) = k3_xboole_0(A_1187,B_1188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_52490])).

tff(c_52914,plain,(
    ! [A_1187,B_1188] :
      ( r2_hidden('#skF_4'(A_1187,B_1188,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_3'(A_1187,B_1188,k1_xboole_0),A_1187)
      | k3_xboole_0(A_1187,B_1188) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_199,c_52823])).

tff(c_56505,plain,(
    ! [A_1242,B_1243] :
      ( r2_hidden('#skF_3'(A_1242,B_1243,k1_xboole_0),A_1242)
      | k3_xboole_0(A_1242,B_1243) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_1489,c_52914])).

tff(c_34,plain,(
    ! [D_23,B_19,A_18] :
      ( ~ r2_hidden(D_23,B_19)
      | ~ r2_hidden(D_23,k4_xboole_0(A_18,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1598,plain,(
    ! [A_193,A_18,B_19,C_195] :
      ( ~ r2_hidden('#skF_3'(A_193,k4_xboole_0(A_18,B_19),C_195),B_19)
      | r2_hidden('#skF_4'(A_193,k4_xboole_0(A_18,B_19),C_195),C_195)
      | k3_xboole_0(A_193,k4_xboole_0(A_18,B_19)) = C_195 ) ),
    inference(resolution,[status(thm)],[c_1537,c_34])).

tff(c_56508,plain,(
    ! [A_1242,A_18] :
      ( r2_hidden('#skF_4'(A_1242,k4_xboole_0(A_18,A_1242),k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(A_1242,k4_xboole_0(A_18,A_1242)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56505,c_1598])).

tff(c_56603,plain,(
    ! [A_1244,A_1245] : k3_xboole_0(A_1244,k4_xboole_0(A_1245,A_1244)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1489,c_56508])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_230,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(A_69,B_70) = A_69
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_234,plain,(
    ! [B_35] : k3_xboole_0(B_35,B_35) = B_35 ),
    inference(resolution,[status(thm)],[c_70,c_230])).

tff(c_96,plain,(
    ! [A_47,C_49,B_48,D_50] : k3_xboole_0(k2_zfmisc_1(A_47,C_49),k2_zfmisc_1(B_48,D_50)) = k2_zfmisc_1(k3_xboole_0(A_47,B_48),k3_xboole_0(C_49,D_50)) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_104,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k2_zfmisc_1('#skF_13','#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1234,plain,(
    ! [A_179,C_180,B_181,D_182] : k3_xboole_0(k2_zfmisc_1(A_179,C_180),k2_zfmisc_1(B_181,D_182)) = k2_zfmisc_1(k3_xboole_0(A_179,B_181),k3_xboole_0(C_180,D_182)) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1278,plain,(
    ! [B_181,D_182] : k3_xboole_0(k2_zfmisc_1('#skF_13','#skF_14'),k2_zfmisc_1(B_181,D_182)) = k2_zfmisc_1(k3_xboole_0('#skF_11',B_181),k3_xboole_0('#skF_12',D_182)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_1234])).

tff(c_1609,plain,(
    ! [B_196,D_197] : k2_zfmisc_1(k3_xboole_0('#skF_11',B_196),k3_xboole_0('#skF_12',D_197)) = k2_zfmisc_1(k3_xboole_0('#skF_13',B_196),k3_xboole_0('#skF_14',D_197)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1278])).

tff(c_1640,plain,(
    ! [B_196] : k2_zfmisc_1(k3_xboole_0('#skF_13',B_196),k3_xboole_0('#skF_14','#skF_12')) = k2_zfmisc_1(k3_xboole_0('#skF_11',B_196),'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_1609])).

tff(c_1671,plain,(
    ! [B_196] : k2_zfmisc_1(k3_xboole_0('#skF_13',B_196),k3_xboole_0('#skF_12','#skF_14')) = k2_zfmisc_1(k3_xboole_0('#skF_11',B_196),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1640])).

tff(c_56870,plain,(
    ! [A_1245] : k2_zfmisc_1(k3_xboole_0('#skF_11',k4_xboole_0(A_1245,'#skF_13')),'#skF_12') = k2_zfmisc_1(k1_xboole_0,k3_xboole_0('#skF_12','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56603,c_1671])).

tff(c_62400,plain,(
    ! [A_1268] : k2_zfmisc_1(k3_xboole_0('#skF_11',k4_xboole_0(A_1268,'#skF_13')),'#skF_12') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_56870])).

tff(c_1281,plain,(
    ! [A_179,C_180] : k3_xboole_0(k2_zfmisc_1(A_179,C_180),k2_zfmisc_1('#skF_13','#skF_14')) = k2_zfmisc_1(k3_xboole_0(A_179,'#skF_11'),k3_xboole_0(C_180,'#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_1234])).

tff(c_1350,plain,(
    ! [A_186,C_187] : k2_zfmisc_1(k3_xboole_0(A_186,'#skF_11'),k3_xboole_0(C_187,'#skF_12')) = k2_zfmisc_1(k3_xboole_0(A_186,'#skF_13'),k3_xboole_0(C_187,'#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1281])).

tff(c_2390,plain,(
    ! [A_248,C_249] : k2_zfmisc_1(k3_xboole_0(A_248,'#skF_13'),k3_xboole_0(C_249,'#skF_14')) = k2_zfmisc_1(k3_xboole_0('#skF_11',A_248),k3_xboole_0(C_249,'#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1350])).

tff(c_1373,plain,(
    ! [A_186] : k2_zfmisc_1(k3_xboole_0(A_186,'#skF_13'),k3_xboole_0('#skF_12','#skF_14')) = k2_zfmisc_1(k3_xboole_0(A_186,'#skF_11'),'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_1350])).

tff(c_2400,plain,(
    ! [A_248] : k2_zfmisc_1(k3_xboole_0('#skF_11',A_248),k3_xboole_0('#skF_12','#skF_12')) = k2_zfmisc_1(k3_xboole_0(A_248,'#skF_11'),'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_2390,c_1373])).

tff(c_5134,plain,(
    ! [A_327] : k2_zfmisc_1(k3_xboole_0(A_327,'#skF_11'),'#skF_12') = k2_zfmisc_1(k3_xboole_0('#skF_11',A_327),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_2400])).

tff(c_90,plain,(
    ! [B_46,A_45] :
      ( k1_xboole_0 = B_46
      | k1_xboole_0 = A_45
      | k2_zfmisc_1(A_45,B_46) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_5158,plain,(
    ! [A_327] :
      ( k1_xboole_0 = '#skF_12'
      | k3_xboole_0(A_327,'#skF_11') = k1_xboole_0
      | k2_zfmisc_1(k3_xboole_0('#skF_11',A_327),'#skF_12') != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5134,c_90])).

tff(c_5204,plain,(
    ! [A_327] :
      ( k3_xboole_0(A_327,'#skF_11') = k1_xboole_0
      | k2_zfmisc_1(k3_xboole_0('#skF_11',A_327),'#skF_12') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_5158])).

tff(c_62485,plain,(
    ! [A_1269] : k3_xboole_0(k4_xboole_0(A_1269,'#skF_13'),'#skF_11') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_62400,c_5204])).

tff(c_559,plain,(
    ! [D_117,A_118,B_119] :
      ( r2_hidden(D_117,A_118)
      | ~ r2_hidden(D_117,k4_xboole_0(A_118,B_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_11152,plain,(
    ! [A_490,B_491,B_492] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_490,B_491),B_492),A_490)
      | r1_tarski(k4_xboole_0(A_490,B_491),B_492) ) ),
    inference(resolution,[status(thm)],[c_12,c_559])).

tff(c_11235,plain,(
    ! [A_493,B_494] : r1_tarski(k4_xboole_0(A_493,B_494),A_493) ),
    inference(resolution,[status(thm)],[c_11152,c_10])).

tff(c_72,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = A_36
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_11359,plain,(
    ! [A_493,B_494] : k3_xboole_0(k4_xboole_0(A_493,B_494),A_493) = k4_xboole_0(A_493,B_494) ),
    inference(resolution,[status(thm)],[c_11235,c_72])).

tff(c_62893,plain,(
    k4_xboole_0('#skF_11','#skF_13') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_62485,c_11359])).

tff(c_32,plain,(
    ! [D_23,A_18,B_19] :
      ( r2_hidden(D_23,k4_xboole_0(A_18,B_19))
      | r2_hidden(D_23,B_19)
      | ~ r2_hidden(D_23,A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_63543,plain,(
    ! [D_23] :
      ( r2_hidden(D_23,k1_xboole_0)
      | r2_hidden(D_23,'#skF_13')
      | ~ r2_hidden(D_23,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62893,c_32])).

tff(c_64435,plain,(
    ! [D_1271] :
      ( r2_hidden(D_1271,'#skF_13')
      | ~ r2_hidden(D_1271,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1489,c_63543])).

tff(c_77345,plain,(
    ! [B_1368] :
      ( r2_hidden('#skF_2'('#skF_11',B_1368),'#skF_13')
      | r1_tarski('#skF_11',B_1368) ) ),
    inference(resolution,[status(thm)],[c_12,c_64435])).

tff(c_77368,plain,(
    r1_tarski('#skF_11','#skF_13') ),
    inference(resolution,[status(thm)],[c_77345,c_10])).

tff(c_66,plain,(
    ! [B_35,A_34] :
      ( B_35 = A_34
      | ~ r1_tarski(B_35,A_34)
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_77385,plain,
    ( '#skF_11' = '#skF_13'
    | ~ r1_tarski('#skF_13','#skF_11') ),
    inference(resolution,[status(thm)],[c_77368,c_66])).

tff(c_77399,plain,(
    ~ r1_tarski('#skF_13','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_77385])).

tff(c_11590,plain,(
    ! [A_506,B_507] : k3_xboole_0(k4_xboole_0(A_506,B_507),A_506) = k4_xboole_0(A_506,B_507) ),
    inference(resolution,[status(thm)],[c_11235,c_72])).

tff(c_11795,plain,(
    ! [A_506,B_507] : k3_xboole_0(A_506,k4_xboole_0(A_506,B_507)) = k4_xboole_0(A_506,B_507) ),
    inference(superposition,[status(thm),theory(equality)],[c_11590,c_2])).

tff(c_425,plain,(
    ! [D_104,B_105,A_106] :
      ( r2_hidden(D_104,B_105)
      | ~ r2_hidden(D_104,k3_xboole_0(A_106,B_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12221,plain,(
    ! [A_510,B_511,B_512] :
      ( r2_hidden('#skF_2'(k3_xboole_0(A_510,B_511),B_512),B_511)
      | r1_tarski(k3_xboole_0(A_510,B_511),B_512) ) ),
    inference(resolution,[status(thm)],[c_12,c_425])).

tff(c_12362,plain,(
    ! [A_513,B_514] : r1_tarski(k3_xboole_0(A_513,B_514),B_514) ),
    inference(resolution,[status(thm)],[c_12221,c_10])).

tff(c_14460,plain,(
    ! [A_563,B_564] : k3_xboole_0(k3_xboole_0(A_563,B_564),B_564) = k3_xboole_0(A_563,B_564) ),
    inference(resolution,[status(thm)],[c_12362,c_72])).

tff(c_14876,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_14460])).

tff(c_57105,plain,(
    ! [A_1245,A_1244] : k3_xboole_0(k4_xboole_0(A_1245,A_1244),A_1244) = k3_xboole_0(k1_xboole_0,A_1244) ),
    inference(superposition,[status(thm),theory(equality)],[c_56603,c_14876])).

tff(c_57713,plain,(
    ! [A_1250,A_1251] : k3_xboole_0(k4_xboole_0(A_1250,A_1251),A_1251) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_57105])).

tff(c_4258,plain,(
    ! [A_305,D_306] : k2_zfmisc_1(k3_xboole_0(A_305,'#skF_11'),k3_xboole_0('#skF_12',D_306)) = k2_zfmisc_1(k3_xboole_0('#skF_13',A_305),k3_xboole_0('#skF_14',D_306)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1609])).

tff(c_4374,plain,(
    ! [A_305] : k2_zfmisc_1(k3_xboole_0(A_305,'#skF_11'),k3_xboole_0('#skF_12','#skF_14')) = k2_zfmisc_1(k3_xboole_0('#skF_13',A_305),'#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_4258])).

tff(c_57847,plain,(
    ! [A_1250] : k2_zfmisc_1(k3_xboole_0('#skF_13',k4_xboole_0(A_1250,'#skF_11')),'#skF_14') = k2_zfmisc_1(k1_xboole_0,k3_xboole_0('#skF_12','#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_57713,c_4374])).

tff(c_70639,plain,(
    ! [A_1336] : k2_zfmisc_1(k3_xboole_0('#skF_13',k4_xboole_0(A_1336,'#skF_11')),'#skF_14') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_57847])).

tff(c_70662,plain,(
    k2_zfmisc_1(k4_xboole_0('#skF_13','#skF_11'),'#skF_14') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11795,c_70639])).

tff(c_70736,plain,
    ( k1_xboole_0 = '#skF_14'
    | k4_xboole_0('#skF_13','#skF_11') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_70662,c_90])).

tff(c_70739,plain,(
    k4_xboole_0('#skF_13','#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_70736])).

tff(c_71038,plain,(
    ! [D_23] :
      ( r2_hidden(D_23,k1_xboole_0)
      | r2_hidden(D_23,'#skF_11')
      | ~ r2_hidden(D_23,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70739,c_32])).

tff(c_71146,plain,(
    ! [D_1337] :
      ( r2_hidden(D_1337,'#skF_11')
      | ~ r2_hidden(D_1337,'#skF_13') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1489,c_71038])).

tff(c_90984,plain,(
    ! [A_1528] :
      ( r1_tarski(A_1528,'#skF_11')
      | ~ r2_hidden('#skF_2'(A_1528,'#skF_11'),'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_71146,c_10])).

tff(c_91016,plain,(
    r1_tarski('#skF_13','#skF_11') ),
    inference(resolution,[status(thm)],[c_12,c_90984])).

tff(c_91026,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77399,c_77399,c_91016])).

tff(c_91027,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_70736])).

tff(c_92,plain,(
    ! [A_45] : k2_zfmisc_1(A_45,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1636,plain,(
    ! [D_197] : k2_zfmisc_1(k3_xboole_0('#skF_13','#skF_11'),k3_xboole_0('#skF_14',D_197)) = k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12',D_197)) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_1609])).

tff(c_57326,plain,(
    ! [A_1245] : k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12',k4_xboole_0(A_1245,'#skF_14'))) = k2_zfmisc_1(k3_xboole_0('#skF_13','#skF_11'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_56603,c_1636])).

tff(c_59017,plain,(
    ! [A_1254] : k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12',k4_xboole_0(A_1254,'#skF_14'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_57326])).

tff(c_102,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_14311,plain,(
    ! [D_561,B_562] :
      ( k3_xboole_0('#skF_12',D_561) = k1_xboole_0
      | k3_xboole_0('#skF_11',B_562) = k1_xboole_0
      | k2_zfmisc_1(k3_xboole_0('#skF_13',B_562),k3_xboole_0('#skF_14',D_561)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1609,c_90])).

tff(c_14389,plain,(
    ! [D_197] :
      ( k3_xboole_0('#skF_12',D_197) = k1_xboole_0
      | k3_xboole_0('#skF_11','#skF_11') = k1_xboole_0
      | k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12',D_197)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1636,c_14311])).

tff(c_14451,plain,(
    ! [D_197] :
      ( k3_xboole_0('#skF_12',D_197) = k1_xboole_0
      | k1_xboole_0 = '#skF_11'
      | k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12',D_197)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_14389])).

tff(c_14452,plain,(
    ! [D_197] :
      ( k3_xboole_0('#skF_12',D_197) = k1_xboole_0
      | k2_zfmisc_1('#skF_11',k3_xboole_0('#skF_12',D_197)) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_14451])).

tff(c_59125,plain,(
    ! [A_1255] : k3_xboole_0('#skF_12',k4_xboole_0(A_1255,'#skF_14')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_59017,c_14452])).

tff(c_59538,plain,(
    k4_xboole_0('#skF_12','#skF_14') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_59125,c_11795])).

tff(c_60625,plain,(
    ! [D_23] :
      ( r2_hidden(D_23,k1_xboole_0)
      | r2_hidden(D_23,'#skF_14')
      | ~ r2_hidden(D_23,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59538,c_32])).

tff(c_61524,plain,(
    ! [D_1261] :
      ( r2_hidden(D_1261,'#skF_14')
      | ~ r2_hidden(D_1261,'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1489,c_60625])).

tff(c_60,plain,(
    ! [A_26,B_27] :
      ( r2_hidden('#skF_7'(A_26,B_27),A_26)
      | r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6994,plain,(
    ! [A_371,B_372,B_373] :
      ( r2_hidden('#skF_7'(A_371,B_372),B_373)
      | ~ r1_tarski(A_371,B_373)
      | r1_xboole_0(A_371,B_372) ) ),
    inference(resolution,[status(thm)],[c_60,c_663])).

tff(c_7043,plain,(
    ! [A_374,B_375] :
      ( ~ r1_tarski(A_374,k1_xboole_0)
      | r1_xboole_0(A_374,B_375) ) ),
    inference(resolution,[status(thm)],[c_6994,c_1489])).

tff(c_56,plain,(
    ! [A_26,B_27,C_30] :
      ( ~ r1_xboole_0(A_26,B_27)
      | ~ r2_hidden(C_30,B_27)
      | ~ r2_hidden(C_30,A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_7061,plain,(
    ! [C_379,B_380,A_381] :
      ( ~ r2_hidden(C_379,B_380)
      | ~ r2_hidden(C_379,A_381)
      | ~ r1_tarski(A_381,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7043,c_56])).

tff(c_7142,plain,(
    ! [C_44,A_381] :
      ( ~ r2_hidden(C_44,A_381)
      | ~ r1_tarski(A_381,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_80,c_7061])).

tff(c_61656,plain,(
    ! [D_1261] :
      ( ~ r1_tarski('#skF_14',k1_xboole_0)
      | ~ r2_hidden(D_1261,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_61524,c_7142])).

tff(c_61933,plain,(
    ~ r1_tarski('#skF_14',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_61656])).

tff(c_91346,plain,(
    ~ r1_tarski('#skF_14','#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91027,c_61933])).

tff(c_91480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_91346])).

tff(c_91483,plain,(
    ! [D_1533] : ~ r2_hidden(D_1533,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_61656])).

tff(c_91507,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_55726,c_91483])).

tff(c_91801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_91507])).

tff(c_91802,plain,(
    '#skF_14' != '#skF_12' ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_91844,plain,(
    ! [B_1538,A_1539] :
      ( ~ r2_hidden(B_1538,A_1539)
      | ~ v1_xboole_0(A_1539) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91848,plain,(
    ! [C_44] : ~ v1_xboole_0(k1_tarski(C_44)) ),
    inference(resolution,[status(thm)],[c_80,c_91844])).

tff(c_91859,plain,(
    ! [C_1542,A_1543] :
      ( C_1542 = A_1543
      | ~ r2_hidden(C_1542,k1_tarski(A_1543)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_91863,plain,(
    ! [A_1543] :
      ( '#skF_1'(k1_tarski(A_1543)) = A_1543
      | v1_xboole_0(k1_tarski(A_1543)) ) ),
    inference(resolution,[status(thm)],[c_6,c_91859])).

tff(c_91869,plain,(
    ! [A_1543] : '#skF_1'(k1_tarski(A_1543)) = A_1543 ),
    inference(negUnitSimplification,[status(thm)],[c_91848,c_91863])).

tff(c_92380,plain,(
    ! [C_1609,B_1610,A_1611] :
      ( r2_hidden(C_1609,B_1610)
      | ~ r2_hidden(C_1609,A_1611)
      | ~ r1_tarski(A_1611,B_1610) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_92572,plain,(
    ! [A_1630,B_1631] :
      ( r2_hidden('#skF_1'(A_1630),B_1631)
      | ~ r1_tarski(A_1630,B_1631)
      | v1_xboole_0(A_1630) ) ),
    inference(resolution,[status(thm)],[c_6,c_92380])).

tff(c_92329,plain,(
    ! [A_1602,B_1603,C_1604] :
      ( ~ r1_xboole_0(A_1602,B_1603)
      | ~ r2_hidden(C_1604,B_1603)
      | ~ r2_hidden(C_1604,A_1602) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_92338,plain,(
    ! [C_1604,A_39] :
      ( ~ r2_hidden(C_1604,k1_xboole_0)
      | ~ r2_hidden(C_1604,A_39) ) ),
    inference(resolution,[status(thm)],[c_76,c_92329])).

tff(c_92970,plain,(
    ! [A_1659,A_1660] :
      ( ~ r2_hidden('#skF_1'(A_1659),A_1660)
      | ~ r1_tarski(A_1659,k1_xboole_0)
      | v1_xboole_0(A_1659) ) ),
    inference(resolution,[status(thm)],[c_92572,c_92338])).

tff(c_92984,plain,(
    ! [A_1543,A_1660] :
      ( ~ r2_hidden(A_1543,A_1660)
      | ~ r1_tarski(k1_tarski(A_1543),k1_xboole_0)
      | v1_xboole_0(k1_tarski(A_1543)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91869,c_92970])).

tff(c_93070,plain,(
    ! [A_1666,A_1667] :
      ( ~ r2_hidden(A_1666,A_1667)
      | ~ r1_tarski(k1_tarski(A_1666),k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_91848,c_92984])).

tff(c_93103,plain,(
    ! [C_44] : ~ r1_tarski(k1_tarski(C_44),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_80,c_93070])).

tff(c_92066,plain,(
    ! [A_1567,B_1568] :
      ( r2_hidden('#skF_2'(A_1567,B_1568),A_1567)
      | r1_tarski(A_1567,B_1568) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_92084,plain,(
    ! [A_40,B_1568] :
      ( '#skF_2'(k1_tarski(A_40),B_1568) = A_40
      | r1_tarski(k1_tarski(A_40),B_1568) ) ),
    inference(resolution,[status(thm)],[c_92066,c_78])).

tff(c_92997,plain,(
    ! [A_1661] :
      ( ~ r1_tarski(A_1661,k1_xboole_0)
      | v1_xboole_0(A_1661) ) ),
    inference(resolution,[status(thm)],[c_6,c_92970])).

tff(c_93001,plain,(
    ! [A_40] :
      ( v1_xboole_0(k1_tarski(A_40))
      | '#skF_2'(k1_tarski(A_40),k1_xboole_0) = A_40 ) ),
    inference(resolution,[status(thm)],[c_92084,c_92997])).

tff(c_93032,plain,(
    ! [A_1665] : '#skF_2'(k1_tarski(A_1665),k1_xboole_0) = A_1665 ),
    inference(negUnitSimplification,[status(thm)],[c_91848,c_93001])).

tff(c_93044,plain,(
    ! [A_1665] :
      ( ~ r2_hidden(A_1665,k1_xboole_0)
      | r1_tarski(k1_tarski(A_1665),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93032,c_10])).

tff(c_93171,plain,(
    ! [A_1665] : ~ r2_hidden(A_1665,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_93103,c_93044])).

tff(c_91887,plain,(
    ! [B_1547,A_1548] : k3_xboole_0(B_1547,A_1548) = k3_xboole_0(A_1548,B_1547) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_91903,plain,(
    ! [A_1548] : k3_xboole_0(k1_xboole_0,A_1548) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_91887,c_74])).

tff(c_93796,plain,(
    ! [A_1704,B_1705,C_1706] :
      ( r2_hidden('#skF_3'(A_1704,B_1705,C_1706),A_1704)
      | r2_hidden('#skF_4'(A_1704,B_1705,C_1706),C_1706)
      | k3_xboole_0(A_1704,B_1705) = C_1706 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_143145,plain,(
    ! [A_2700,B_2701,A_2702,B_2703] :
      ( r2_hidden('#skF_4'(A_2700,B_2701,k3_xboole_0(A_2702,B_2703)),A_2702)
      | r2_hidden('#skF_3'(A_2700,B_2701,k3_xboole_0(A_2702,B_2703)),A_2700)
      | k3_xboole_0(A_2702,B_2703) = k3_xboole_0(A_2700,B_2701) ) ),
    inference(resolution,[status(thm)],[c_93796,c_18])).

tff(c_143434,plain,(
    ! [A_2700,B_2701,A_1548] :
      ( r2_hidden('#skF_4'(A_2700,B_2701,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_3'(A_2700,B_2701,k3_xboole_0(k1_xboole_0,A_1548)),A_2700)
      | k3_xboole_0(k1_xboole_0,A_1548) = k3_xboole_0(A_2700,B_2701) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91903,c_143145])).

tff(c_143513,plain,(
    ! [A_2700,B_2701] :
      ( r2_hidden('#skF_4'(A_2700,B_2701,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_3'(A_2700,B_2701,k1_xboole_0),A_2700)
      | k3_xboole_0(A_2700,B_2701) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91903,c_91903,c_143434])).

tff(c_147053,plain,(
    ! [A_2764,B_2765] :
      ( r2_hidden('#skF_3'(A_2764,B_2765,k1_xboole_0),A_2764)
      | k3_xboole_0(A_2764,B_2765) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_93171,c_143513])).

tff(c_93278,plain,(
    ! [A_1676,B_1677,C_1678] :
      ( r2_hidden('#skF_3'(A_1676,B_1677,C_1678),B_1677)
      | r2_hidden('#skF_4'(A_1676,B_1677,C_1678),C_1678)
      | k3_xboole_0(A_1676,B_1677) = C_1678 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_93338,plain,(
    ! [A_1676,A_18,B_19,C_1678] :
      ( ~ r2_hidden('#skF_3'(A_1676,k4_xboole_0(A_18,B_19),C_1678),B_19)
      | r2_hidden('#skF_4'(A_1676,k4_xboole_0(A_18,B_19),C_1678),C_1678)
      | k3_xboole_0(A_1676,k4_xboole_0(A_18,B_19)) = C_1678 ) ),
    inference(resolution,[status(thm)],[c_93278,c_34])).

tff(c_147056,plain,(
    ! [A_2764,A_18] :
      ( r2_hidden('#skF_4'(A_2764,k4_xboole_0(A_18,A_2764),k1_xboole_0),k1_xboole_0)
      | k3_xboole_0(A_2764,k4_xboole_0(A_18,A_2764)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_147053,c_93338])).

tff(c_147123,plain,(
    ! [A_2766,A_2767] : k3_xboole_0(A_2766,k4_xboole_0(A_2767,A_2766)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_93171,c_147056])).

tff(c_91803,plain,(
    '#skF_11' = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_91809,plain,(
    k1_xboole_0 != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91803,c_102])).

tff(c_91967,plain,(
    ! [A_1550,B_1551] :
      ( k3_xboole_0(A_1550,B_1551) = A_1550
      | ~ r1_tarski(A_1550,B_1551) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_91971,plain,(
    ! [B_35] : k3_xboole_0(B_35,B_35) = B_35 ),
    inference(resolution,[status(thm)],[c_70,c_91967])).

tff(c_91808,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') = k2_zfmisc_1('#skF_13','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91803,c_104])).

tff(c_92901,plain,(
    ! [A_1653,C_1654,B_1655,D_1656] : k3_xboole_0(k2_zfmisc_1(A_1653,C_1654),k2_zfmisc_1(B_1655,D_1656)) = k2_zfmisc_1(k3_xboole_0(A_1653,B_1655),k3_xboole_0(C_1654,D_1656)) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_92939,plain,(
    ! [B_1655,D_1656] : k3_xboole_0(k2_zfmisc_1('#skF_13','#skF_12'),k2_zfmisc_1(B_1655,D_1656)) = k2_zfmisc_1(k3_xboole_0('#skF_13',B_1655),k3_xboole_0('#skF_14',D_1656)) ),
    inference(superposition,[status(thm),theory(equality)],[c_91808,c_92901])).

tff(c_93350,plain,(
    ! [B_1679,D_1680] : k2_zfmisc_1(k3_xboole_0('#skF_13',B_1679),k3_xboole_0('#skF_14',D_1680)) = k2_zfmisc_1(k3_xboole_0('#skF_13',B_1679),k3_xboole_0('#skF_12',D_1680)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92939])).

tff(c_93377,plain,(
    ! [D_1680] : k2_zfmisc_1(k3_xboole_0('#skF_13','#skF_13'),k3_xboole_0('#skF_12',D_1680)) = k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_14',D_1680)) ),
    inference(superposition,[status(thm),theory(equality)],[c_91971,c_93350])).

tff(c_96515,plain,(
    ! [D_1798] : k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_14',D_1798)) = k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_12',D_1798)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91971,c_93377])).

tff(c_96527,plain,(
    ! [D_1798] :
      ( k3_xboole_0('#skF_14',D_1798) = k1_xboole_0
      | k1_xboole_0 = '#skF_13'
      | k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_12',D_1798)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96515,c_90])).

tff(c_96562,plain,(
    ! [D_1798] :
      ( k3_xboole_0('#skF_14',D_1798) = k1_xboole_0
      | k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_12',D_1798)) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_91809,c_96527])).

tff(c_147794,plain,(
    ! [A_2767] :
      ( k3_xboole_0('#skF_14',k4_xboole_0(A_2767,'#skF_12')) = k1_xboole_0
      | k2_zfmisc_1('#skF_13',k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147123,c_96562])).

tff(c_148235,plain,(
    ! [A_2768] : k3_xboole_0('#skF_14',k4_xboole_0(A_2768,'#skF_12')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_147794])).

tff(c_36,plain,(
    ! [D_23,A_18,B_19] :
      ( r2_hidden(D_23,A_18)
      | ~ r2_hidden(D_23,k4_xboole_0(A_18,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_112773,plain,(
    ! [A_2125,B_2126,B_2127] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_2125,B_2126),B_2127),A_2125)
      | r1_tarski(k4_xboole_0(A_2125,B_2126),B_2127) ) ),
    inference(resolution,[status(thm)],[c_92066,c_36])).

tff(c_112851,plain,(
    ! [A_2128,B_2129] : r1_tarski(k4_xboole_0(A_2128,B_2129),A_2128) ),
    inference(resolution,[status(thm)],[c_112773,c_10])).

tff(c_113189,plain,(
    ! [A_2138,B_2139] : k3_xboole_0(k4_xboole_0(A_2138,B_2139),A_2138) = k4_xboole_0(A_2138,B_2139) ),
    inference(resolution,[status(thm)],[c_112851,c_72])).

tff(c_113541,plain,(
    ! [A_2138,B_2139] : k3_xboole_0(A_2138,k4_xboole_0(A_2138,B_2139)) = k4_xboole_0(A_2138,B_2139) ),
    inference(superposition,[status(thm),theory(equality)],[c_113189,c_2])).

tff(c_148554,plain,(
    k4_xboole_0('#skF_14','#skF_12') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_148235,c_113541])).

tff(c_149420,plain,(
    ! [D_23] :
      ( r2_hidden(D_23,k1_xboole_0)
      | r2_hidden(D_23,'#skF_12')
      | ~ r2_hidden(D_23,'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148554,c_32])).

tff(c_151756,plain,(
    ! [D_2777] :
      ( r2_hidden(D_2777,'#skF_12')
      | ~ r2_hidden(D_2777,'#skF_14') ) ),
    inference(negUnitSimplification,[status(thm)],[c_93171,c_149420])).

tff(c_159300,plain,(
    ! [B_2846] :
      ( r2_hidden('#skF_2'('#skF_14',B_2846),'#skF_12')
      | r1_tarski('#skF_14',B_2846) ) ),
    inference(resolution,[status(thm)],[c_12,c_151756])).

tff(c_159323,plain,(
    r1_tarski('#skF_14','#skF_12') ),
    inference(resolution,[status(thm)],[c_159300,c_10])).

tff(c_50,plain,(
    ! [A_24,B_25] :
      ( r2_xboole_0(A_24,B_25)
      | B_25 = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_64,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_8'(A_31,B_32),B_32)
      | ~ r2_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_93412,plain,(
    ! [D_1680] : k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_14',D_1680)) = k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_12',D_1680)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91971,c_93377])).

tff(c_147804,plain,(
    ! [A_2767] : k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_12',k4_xboole_0(A_2767,'#skF_14'))) = k2_zfmisc_1('#skF_13',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_147123,c_93412])).

tff(c_154275,plain,(
    ! [A_2807] : k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_12',k4_xboole_0(A_2807,'#skF_14'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_147804])).

tff(c_92942,plain,(
    ! [A_1653,C_1654] : k3_xboole_0(k2_zfmisc_1(A_1653,C_1654),k2_zfmisc_1('#skF_13','#skF_12')) = k2_zfmisc_1(k3_xboole_0(A_1653,'#skF_13'),k3_xboole_0(C_1654,'#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_91808,c_92901])).

tff(c_93115,plain,(
    ! [A_1669,C_1670] : k2_zfmisc_1(k3_xboole_0(A_1669,'#skF_13'),k3_xboole_0(C_1670,'#skF_14')) = k2_zfmisc_1(k3_xboole_0(A_1669,'#skF_13'),k3_xboole_0(C_1670,'#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92942])).

tff(c_93134,plain,(
    ! [C_1670] : k2_zfmisc_1(k3_xboole_0('#skF_13','#skF_13'),k3_xboole_0(C_1670,'#skF_12')) = k2_zfmisc_1('#skF_13',k3_xboole_0(C_1670,'#skF_14')) ),
    inference(superposition,[status(thm),theory(equality)],[c_91971,c_93115])).

tff(c_96723,plain,(
    ! [C_1805] : k2_zfmisc_1('#skF_13',k3_xboole_0(C_1805,'#skF_14')) = k2_zfmisc_1('#skF_13',k3_xboole_0(C_1805,'#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91971,c_93134])).

tff(c_96922,plain,(
    ! [B_1809] : k2_zfmisc_1('#skF_13',k3_xboole_0(B_1809,'#skF_12')) = k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_14',B_1809)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_96723])).

tff(c_96953,plain,(
    ! [B_1809] :
      ( k3_xboole_0(B_1809,'#skF_12') = k1_xboole_0
      | k1_xboole_0 = '#skF_13'
      | k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_14',B_1809)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96922,c_90])).

tff(c_97009,plain,(
    ! [B_1809] :
      ( k3_xboole_0(B_1809,'#skF_12') = k1_xboole_0
      | k1_xboole_0 = '#skF_13'
      | k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_12',B_1809)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93412,c_96953])).

tff(c_97010,plain,(
    ! [B_1809] :
      ( k3_xboole_0(B_1809,'#skF_12') = k1_xboole_0
      | k2_zfmisc_1('#skF_13',k3_xboole_0('#skF_12',B_1809)) != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_91809,c_97009])).

tff(c_154366,plain,(
    ! [A_2808] : k3_xboole_0(k4_xboole_0(A_2808,'#skF_14'),'#skF_12') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_154275,c_97010])).

tff(c_112977,plain,(
    ! [A_2128,B_2129] : k3_xboole_0(k4_xboole_0(A_2128,B_2129),A_2128) = k4_xboole_0(A_2128,B_2129) ),
    inference(resolution,[status(thm)],[c_112851,c_72])).

tff(c_154718,plain,(
    k4_xboole_0('#skF_12','#skF_14') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_154366,c_112977])).

tff(c_155536,plain,(
    ! [D_23] :
      ( r2_hidden(D_23,k1_xboole_0)
      | r2_hidden(D_23,'#skF_14')
      | ~ r2_hidden(D_23,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154718,c_32])).

tff(c_156782,plain,(
    ! [D_2816] :
      ( r2_hidden(D_2816,'#skF_14')
      | ~ r2_hidden(D_2816,'#skF_12') ) ),
    inference(negUnitSimplification,[status(thm)],[c_93171,c_155536])).

tff(c_62,plain,(
    ! [A_31,B_32] :
      ( ~ r2_hidden('#skF_8'(A_31,B_32),A_31)
      | ~ r2_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_161853,plain,(
    ! [B_2862] :
      ( ~ r2_xboole_0('#skF_14',B_2862)
      | ~ r2_hidden('#skF_8'('#skF_14',B_2862),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_156782,c_62])).

tff(c_161883,plain,(
    ~ r2_xboole_0('#skF_14','#skF_12') ),
    inference(resolution,[status(thm)],[c_64,c_161853])).

tff(c_162233,plain,
    ( '#skF_14' = '#skF_12'
    | ~ r1_tarski('#skF_14','#skF_12') ),
    inference(resolution,[status(thm)],[c_50,c_161883])).

tff(c_162236,plain,(
    '#skF_14' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159323,c_162233])).

tff(c_162238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91802,c_162236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.26/25.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.42/25.55  
% 36.42/25.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.42/25.55  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_14 > #skF_13 > #skF_5 > #skF_10 > #skF_8 > #skF_3 > #skF_2 > #skF_7 > #skF_9 > #skF_12
% 36.42/25.55  
% 36.42/25.55  %Foreground sorts:
% 36.42/25.55  
% 36.42/25.55  
% 36.42/25.55  %Background operators:
% 36.42/25.55  
% 36.42/25.55  
% 36.42/25.55  %Foreground operators:
% 36.42/25.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.42/25.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 36.42/25.55  tff('#skF_11', type, '#skF_11': $i).
% 36.42/25.55  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 36.42/25.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 36.42/25.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 36.42/25.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 36.42/25.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 36.42/25.55  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 36.42/25.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 36.42/25.55  tff('#skF_14', type, '#skF_14': $i).
% 36.42/25.55  tff('#skF_13', type, '#skF_13': $i).
% 36.42/25.55  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 36.42/25.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 36.42/25.55  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 36.42/25.55  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 36.42/25.55  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 36.42/25.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.42/25.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 36.42/25.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 36.42/25.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.42/25.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 36.42/25.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 36.42/25.55  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 36.42/25.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 36.42/25.55  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 36.42/25.55  tff('#skF_12', type, '#skF_12': $i).
% 36.42/25.55  
% 36.42/25.59  tff(f_134, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 36.42/25.59  tff(f_115, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 36.42/25.59  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 36.42/25.59  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 36.42/25.59  tff(f_108, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 36.42/25.59  tff(f_84, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 36.42/25.59  tff(f_106, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 36.42/25.59  tff(f_49, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 36.42/25.59  tff(f_100, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 36.42/25.59  tff(f_121, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 36.42/25.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 36.42/25.59  tff(f_59, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 36.42/25.59  tff(f_104, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 36.42/25.59  tff(f_123, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 36.42/25.59  tff(f_66, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 36.42/25.59  tff(f_94, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 36.42/25.59  tff(c_100, plain, (k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_134])).
% 36.42/25.59  tff(c_80, plain, (![C_44]: (r2_hidden(C_44, k1_tarski(C_44)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 36.42/25.59  tff(c_144, plain, (![B_58, A_59]: (~r2_hidden(B_58, A_59) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_33])).
% 36.42/25.59  tff(c_148, plain, (![C_44]: (~v1_xboole_0(k1_tarski(C_44)))), inference(resolution, [status(thm)], [c_80, c_144])).
% 36.42/25.59  tff(c_156, plain, (![A_63]: (v1_xboole_0(A_63) | r2_hidden('#skF_1'(A_63), A_63))), inference(cnfTransformation, [status(thm)], [f_33])).
% 36.42/25.59  tff(c_78, plain, (![C_44, A_40]: (C_44=A_40 | ~r2_hidden(C_44, k1_tarski(A_40)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 36.42/25.59  tff(c_160, plain, (![A_40]: ('#skF_1'(k1_tarski(A_40))=A_40 | v1_xboole_0(k1_tarski(A_40)))), inference(resolution, [status(thm)], [c_156, c_78])).
% 36.42/25.59  tff(c_166, plain, (![A_40]: ('#skF_1'(k1_tarski(A_40))=A_40)), inference(negUnitSimplification, [status(thm)], [c_148, c_160])).
% 36.42/25.59  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 36.42/25.59  tff(c_663, plain, (![C_128, B_129, A_130]: (r2_hidden(C_128, B_129) | ~r2_hidden(C_128, A_130) | ~r1_tarski(A_130, B_129))), inference(cnfTransformation, [status(thm)], [f_40])).
% 36.42/25.59  tff(c_917, plain, (![A_161, B_162]: (r2_hidden('#skF_1'(A_161), B_162) | ~r1_tarski(A_161, B_162) | v1_xboole_0(A_161))), inference(resolution, [status(thm)], [c_6, c_663])).
% 36.42/25.59  tff(c_76, plain, (![A_39]: (r1_xboole_0(A_39, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_108])).
% 36.42/25.59  tff(c_624, plain, (![A_122, B_123, C_124]: (~r1_xboole_0(A_122, B_123) | ~r2_hidden(C_124, B_123) | ~r2_hidden(C_124, A_122))), inference(cnfTransformation, [status(thm)], [f_84])).
% 36.42/25.59  tff(c_633, plain, (![C_124, A_39]: (~r2_hidden(C_124, k1_xboole_0) | ~r2_hidden(C_124, A_39))), inference(resolution, [status(thm)], [c_76, c_624])).
% 36.42/25.59  tff(c_1298, plain, (![A_183, A_184]: (~r2_hidden('#skF_1'(A_183), A_184) | ~r1_tarski(A_183, k1_xboole_0) | v1_xboole_0(A_183))), inference(resolution, [status(thm)], [c_917, c_633])).
% 36.42/25.59  tff(c_1312, plain, (![A_40, A_184]: (~r2_hidden(A_40, A_184) | ~r1_tarski(k1_tarski(A_40), k1_xboole_0) | v1_xboole_0(k1_tarski(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_166, c_1298])).
% 36.42/25.59  tff(c_1444, plain, (![A_189, A_190]: (~r2_hidden(A_189, A_190) | ~r1_tarski(k1_tarski(A_189), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_148, c_1312])).
% 36.42/25.59  tff(c_1477, plain, (![C_44]: (~r1_tarski(k1_tarski(C_44), k1_xboole_0))), inference(resolution, [status(thm)], [c_80, c_1444])).
% 36.42/25.59  tff(c_336, plain, (![A_81, B_82]: (r2_hidden('#skF_2'(A_81, B_82), A_81) | r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_40])).
% 36.42/25.59  tff(c_350, plain, (![A_40, B_82]: ('#skF_2'(k1_tarski(A_40), B_82)=A_40 | r1_tarski(k1_tarski(A_40), B_82))), inference(resolution, [status(thm)], [c_336, c_78])).
% 36.42/25.59  tff(c_1325, plain, (![A_185]: (~r1_tarski(A_185, k1_xboole_0) | v1_xboole_0(A_185))), inference(resolution, [status(thm)], [c_6, c_1298])).
% 36.42/25.59  tff(c_1329, plain, (![A_40]: (v1_xboole_0(k1_tarski(A_40)) | '#skF_2'(k1_tarski(A_40), k1_xboole_0)=A_40)), inference(resolution, [status(thm)], [c_350, c_1325])).
% 36.42/25.59  tff(c_1406, plain, (![A_188]: ('#skF_2'(k1_tarski(A_188), k1_xboole_0)=A_188)), inference(negUnitSimplification, [status(thm)], [c_148, c_1329])).
% 36.42/25.59  tff(c_10, plain, (![A_7, B_8]: (~r2_hidden('#skF_2'(A_7, B_8), B_8) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 36.42/25.59  tff(c_1421, plain, (![A_188]: (~r2_hidden(A_188, k1_xboole_0) | r1_tarski(k1_tarski(A_188), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1406, c_10])).
% 36.42/25.59  tff(c_1489, plain, (![A_188]: (~r2_hidden(A_188, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_1477, c_1421])).
% 36.42/25.59  tff(c_74, plain, (![A_38]: (k3_xboole_0(A_38, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_106])).
% 36.42/25.59  tff(c_1537, plain, (![A_193, B_194, C_195]: (r2_hidden('#skF_3'(A_193, B_194, C_195), B_194) | r2_hidden('#skF_4'(A_193, B_194, C_195), C_195) | k3_xboole_0(A_193, B_194)=C_195)), inference(cnfTransformation, [status(thm)], [f_49])).
% 36.42/25.59  tff(c_16, plain, (![D_17, B_13, A_12]: (r2_hidden(D_17, B_13) | ~r2_hidden(D_17, k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 36.42/25.59  tff(c_55301, plain, (![A_1220, A_1221, B_1222, C_1223]: (r2_hidden('#skF_3'(A_1220, k3_xboole_0(A_1221, B_1222), C_1223), B_1222) | r2_hidden('#skF_4'(A_1220, k3_xboole_0(A_1221, B_1222), C_1223), C_1223) | k3_xboole_0(A_1220, k3_xboole_0(A_1221, B_1222))=C_1223)), inference(resolution, [status(thm)], [c_1537, c_16])).
% 36.42/25.59  tff(c_55655, plain, (![A_1220, A_38, C_1223]: (r2_hidden('#skF_3'(A_1220, k3_xboole_0(A_38, k1_xboole_0), C_1223), k1_xboole_0) | r2_hidden('#skF_4'(A_1220, k1_xboole_0, C_1223), C_1223) | k3_xboole_0(A_1220, k3_xboole_0(A_38, k1_xboole_0))=C_1223)), inference(superposition, [status(thm), theory('equality')], [c_74, c_55301])).
% 36.42/25.59  tff(c_55725, plain, (![A_1220, C_1223]: (r2_hidden('#skF_3'(A_1220, k1_xboole_0, C_1223), k1_xboole_0) | r2_hidden('#skF_4'(A_1220, k1_xboole_0, C_1223), C_1223) | k1_xboole_0=C_1223)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_74, c_55655])).
% 36.42/25.59  tff(c_55726, plain, (![A_1220, C_1223]: (r2_hidden('#skF_4'(A_1220, k1_xboole_0, C_1223), C_1223) | k1_xboole_0=C_1223)), inference(negUnitSimplification, [status(thm)], [c_1489, c_55725])).
% 36.42/25.59  tff(c_70, plain, (![B_35]: (r1_tarski(B_35, B_35))), inference(cnfTransformation, [status(thm)], [f_100])).
% 36.42/25.59  tff(c_98, plain, ('#skF_14'!='#skF_12' | '#skF_11'!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_134])).
% 36.42/25.59  tff(c_109, plain, ('#skF_11'!='#skF_13'), inference(splitLeft, [status(thm)], [c_98])).
% 36.42/25.59  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), A_7) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 36.42/25.59  tff(c_94, plain, (![B_46]: (k2_zfmisc_1(k1_xboole_0, B_46)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_121])).
% 36.42/25.59  tff(c_183, plain, (![B_67, A_68]: (k3_xboole_0(B_67, A_68)=k3_xboole_0(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_27])).
% 36.42/25.59  tff(c_199, plain, (![A_68]: (k3_xboole_0(k1_xboole_0, A_68)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_183, c_74])).
% 36.42/25.59  tff(c_3558, plain, (![A_276, B_277, C_278]: (r2_hidden('#skF_3'(A_276, B_277, C_278), A_276) | r2_hidden('#skF_4'(A_276, B_277, C_278), C_278) | k3_xboole_0(A_276, B_277)=C_278)), inference(cnfTransformation, [status(thm)], [f_49])).
% 36.42/25.59  tff(c_18, plain, (![D_17, A_12, B_13]: (r2_hidden(D_17, A_12) | ~r2_hidden(D_17, k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 36.42/25.59  tff(c_52490, plain, (![A_1187, B_1188, A_1189, B_1190]: (r2_hidden('#skF_4'(A_1187, B_1188, k3_xboole_0(A_1189, B_1190)), A_1189) | r2_hidden('#skF_3'(A_1187, B_1188, k3_xboole_0(A_1189, B_1190)), A_1187) | k3_xboole_0(A_1189, B_1190)=k3_xboole_0(A_1187, B_1188))), inference(resolution, [status(thm)], [c_3558, c_18])).
% 36.42/25.59  tff(c_52823, plain, (![A_1187, B_1188, A_68]: (r2_hidden('#skF_4'(A_1187, B_1188, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_3'(A_1187, B_1188, k3_xboole_0(k1_xboole_0, A_68)), A_1187) | k3_xboole_0(k1_xboole_0, A_68)=k3_xboole_0(A_1187, B_1188))), inference(superposition, [status(thm), theory('equality')], [c_199, c_52490])).
% 36.42/25.59  tff(c_52914, plain, (![A_1187, B_1188]: (r2_hidden('#skF_4'(A_1187, B_1188, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_3'(A_1187, B_1188, k1_xboole_0), A_1187) | k3_xboole_0(A_1187, B_1188)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_199, c_199, c_52823])).
% 36.42/25.59  tff(c_56505, plain, (![A_1242, B_1243]: (r2_hidden('#skF_3'(A_1242, B_1243, k1_xboole_0), A_1242) | k3_xboole_0(A_1242, B_1243)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_1489, c_52914])).
% 36.42/25.59  tff(c_34, plain, (![D_23, B_19, A_18]: (~r2_hidden(D_23, B_19) | ~r2_hidden(D_23, k4_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 36.42/25.59  tff(c_1598, plain, (![A_193, A_18, B_19, C_195]: (~r2_hidden('#skF_3'(A_193, k4_xboole_0(A_18, B_19), C_195), B_19) | r2_hidden('#skF_4'(A_193, k4_xboole_0(A_18, B_19), C_195), C_195) | k3_xboole_0(A_193, k4_xboole_0(A_18, B_19))=C_195)), inference(resolution, [status(thm)], [c_1537, c_34])).
% 36.42/25.59  tff(c_56508, plain, (![A_1242, A_18]: (r2_hidden('#skF_4'(A_1242, k4_xboole_0(A_18, A_1242), k1_xboole_0), k1_xboole_0) | k3_xboole_0(A_1242, k4_xboole_0(A_18, A_1242))=k1_xboole_0)), inference(resolution, [status(thm)], [c_56505, c_1598])).
% 36.42/25.59  tff(c_56603, plain, (![A_1244, A_1245]: (k3_xboole_0(A_1244, k4_xboole_0(A_1245, A_1244))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_1489, c_56508])).
% 36.42/25.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 36.42/25.59  tff(c_230, plain, (![A_69, B_70]: (k3_xboole_0(A_69, B_70)=A_69 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_104])).
% 36.42/25.59  tff(c_234, plain, (![B_35]: (k3_xboole_0(B_35, B_35)=B_35)), inference(resolution, [status(thm)], [c_70, c_230])).
% 36.42/25.59  tff(c_96, plain, (![A_47, C_49, B_48, D_50]: (k3_xboole_0(k2_zfmisc_1(A_47, C_49), k2_zfmisc_1(B_48, D_50))=k2_zfmisc_1(k3_xboole_0(A_47, B_48), k3_xboole_0(C_49, D_50)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 36.42/25.59  tff(c_104, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k2_zfmisc_1('#skF_13', '#skF_14')), inference(cnfTransformation, [status(thm)], [f_134])).
% 36.42/25.59  tff(c_1234, plain, (![A_179, C_180, B_181, D_182]: (k3_xboole_0(k2_zfmisc_1(A_179, C_180), k2_zfmisc_1(B_181, D_182))=k2_zfmisc_1(k3_xboole_0(A_179, B_181), k3_xboole_0(C_180, D_182)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 36.42/25.59  tff(c_1278, plain, (![B_181, D_182]: (k3_xboole_0(k2_zfmisc_1('#skF_13', '#skF_14'), k2_zfmisc_1(B_181, D_182))=k2_zfmisc_1(k3_xboole_0('#skF_11', B_181), k3_xboole_0('#skF_12', D_182)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_1234])).
% 36.42/25.59  tff(c_1609, plain, (![B_196, D_197]: (k2_zfmisc_1(k3_xboole_0('#skF_11', B_196), k3_xboole_0('#skF_12', D_197))=k2_zfmisc_1(k3_xboole_0('#skF_13', B_196), k3_xboole_0('#skF_14', D_197)))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_1278])).
% 36.42/25.59  tff(c_1640, plain, (![B_196]: (k2_zfmisc_1(k3_xboole_0('#skF_13', B_196), k3_xboole_0('#skF_14', '#skF_12'))=k2_zfmisc_1(k3_xboole_0('#skF_11', B_196), '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_1609])).
% 36.42/25.59  tff(c_1671, plain, (![B_196]: (k2_zfmisc_1(k3_xboole_0('#skF_13', B_196), k3_xboole_0('#skF_12', '#skF_14'))=k2_zfmisc_1(k3_xboole_0('#skF_11', B_196), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1640])).
% 36.42/25.59  tff(c_56870, plain, (![A_1245]: (k2_zfmisc_1(k3_xboole_0('#skF_11', k4_xboole_0(A_1245, '#skF_13')), '#skF_12')=k2_zfmisc_1(k1_xboole_0, k3_xboole_0('#skF_12', '#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_56603, c_1671])).
% 36.42/25.59  tff(c_62400, plain, (![A_1268]: (k2_zfmisc_1(k3_xboole_0('#skF_11', k4_xboole_0(A_1268, '#skF_13')), '#skF_12')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_56870])).
% 36.42/25.59  tff(c_1281, plain, (![A_179, C_180]: (k3_xboole_0(k2_zfmisc_1(A_179, C_180), k2_zfmisc_1('#skF_13', '#skF_14'))=k2_zfmisc_1(k3_xboole_0(A_179, '#skF_11'), k3_xboole_0(C_180, '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_104, c_1234])).
% 36.42/25.59  tff(c_1350, plain, (![A_186, C_187]: (k2_zfmisc_1(k3_xboole_0(A_186, '#skF_11'), k3_xboole_0(C_187, '#skF_12'))=k2_zfmisc_1(k3_xboole_0(A_186, '#skF_13'), k3_xboole_0(C_187, '#skF_14')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_1281])).
% 36.42/25.59  tff(c_2390, plain, (![A_248, C_249]: (k2_zfmisc_1(k3_xboole_0(A_248, '#skF_13'), k3_xboole_0(C_249, '#skF_14'))=k2_zfmisc_1(k3_xboole_0('#skF_11', A_248), k3_xboole_0(C_249, '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1350])).
% 36.42/25.59  tff(c_1373, plain, (![A_186]: (k2_zfmisc_1(k3_xboole_0(A_186, '#skF_13'), k3_xboole_0('#skF_12', '#skF_14'))=k2_zfmisc_1(k3_xboole_0(A_186, '#skF_11'), '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_1350])).
% 36.42/25.59  tff(c_2400, plain, (![A_248]: (k2_zfmisc_1(k3_xboole_0('#skF_11', A_248), k3_xboole_0('#skF_12', '#skF_12'))=k2_zfmisc_1(k3_xboole_0(A_248, '#skF_11'), '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_2390, c_1373])).
% 36.42/25.59  tff(c_5134, plain, (![A_327]: (k2_zfmisc_1(k3_xboole_0(A_327, '#skF_11'), '#skF_12')=k2_zfmisc_1(k3_xboole_0('#skF_11', A_327), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_2400])).
% 36.42/25.59  tff(c_90, plain, (![B_46, A_45]: (k1_xboole_0=B_46 | k1_xboole_0=A_45 | k2_zfmisc_1(A_45, B_46)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_121])).
% 36.42/25.59  tff(c_5158, plain, (![A_327]: (k1_xboole_0='#skF_12' | k3_xboole_0(A_327, '#skF_11')=k1_xboole_0 | k2_zfmisc_1(k3_xboole_0('#skF_11', A_327), '#skF_12')!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5134, c_90])).
% 36.42/25.59  tff(c_5204, plain, (![A_327]: (k3_xboole_0(A_327, '#skF_11')=k1_xboole_0 | k2_zfmisc_1(k3_xboole_0('#skF_11', A_327), '#skF_12')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_100, c_5158])).
% 36.42/25.59  tff(c_62485, plain, (![A_1269]: (k3_xboole_0(k4_xboole_0(A_1269, '#skF_13'), '#skF_11')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_62400, c_5204])).
% 36.42/25.59  tff(c_559, plain, (![D_117, A_118, B_119]: (r2_hidden(D_117, A_118) | ~r2_hidden(D_117, k4_xboole_0(A_118, B_119)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 36.42/25.59  tff(c_11152, plain, (![A_490, B_491, B_492]: (r2_hidden('#skF_2'(k4_xboole_0(A_490, B_491), B_492), A_490) | r1_tarski(k4_xboole_0(A_490, B_491), B_492))), inference(resolution, [status(thm)], [c_12, c_559])).
% 36.42/25.59  tff(c_11235, plain, (![A_493, B_494]: (r1_tarski(k4_xboole_0(A_493, B_494), A_493))), inference(resolution, [status(thm)], [c_11152, c_10])).
% 36.42/25.59  tff(c_72, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=A_36 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_104])).
% 36.42/25.59  tff(c_11359, plain, (![A_493, B_494]: (k3_xboole_0(k4_xboole_0(A_493, B_494), A_493)=k4_xboole_0(A_493, B_494))), inference(resolution, [status(thm)], [c_11235, c_72])).
% 36.42/25.59  tff(c_62893, plain, (k4_xboole_0('#skF_11', '#skF_13')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_62485, c_11359])).
% 36.42/25.59  tff(c_32, plain, (![D_23, A_18, B_19]: (r2_hidden(D_23, k4_xboole_0(A_18, B_19)) | r2_hidden(D_23, B_19) | ~r2_hidden(D_23, A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 36.42/25.59  tff(c_63543, plain, (![D_23]: (r2_hidden(D_23, k1_xboole_0) | r2_hidden(D_23, '#skF_13') | ~r2_hidden(D_23, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_62893, c_32])).
% 36.42/25.59  tff(c_64435, plain, (![D_1271]: (r2_hidden(D_1271, '#skF_13') | ~r2_hidden(D_1271, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_1489, c_63543])).
% 36.42/25.59  tff(c_77345, plain, (![B_1368]: (r2_hidden('#skF_2'('#skF_11', B_1368), '#skF_13') | r1_tarski('#skF_11', B_1368))), inference(resolution, [status(thm)], [c_12, c_64435])).
% 36.42/25.59  tff(c_77368, plain, (r1_tarski('#skF_11', '#skF_13')), inference(resolution, [status(thm)], [c_77345, c_10])).
% 36.42/25.59  tff(c_66, plain, (![B_35, A_34]: (B_35=A_34 | ~r1_tarski(B_35, A_34) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_100])).
% 36.42/25.59  tff(c_77385, plain, ('#skF_11'='#skF_13' | ~r1_tarski('#skF_13', '#skF_11')), inference(resolution, [status(thm)], [c_77368, c_66])).
% 36.42/25.59  tff(c_77399, plain, (~r1_tarski('#skF_13', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_109, c_77385])).
% 36.42/25.59  tff(c_11590, plain, (![A_506, B_507]: (k3_xboole_0(k4_xboole_0(A_506, B_507), A_506)=k4_xboole_0(A_506, B_507))), inference(resolution, [status(thm)], [c_11235, c_72])).
% 36.42/25.59  tff(c_11795, plain, (![A_506, B_507]: (k3_xboole_0(A_506, k4_xboole_0(A_506, B_507))=k4_xboole_0(A_506, B_507))), inference(superposition, [status(thm), theory('equality')], [c_11590, c_2])).
% 36.42/25.59  tff(c_425, plain, (![D_104, B_105, A_106]: (r2_hidden(D_104, B_105) | ~r2_hidden(D_104, k3_xboole_0(A_106, B_105)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 36.42/25.59  tff(c_12221, plain, (![A_510, B_511, B_512]: (r2_hidden('#skF_2'(k3_xboole_0(A_510, B_511), B_512), B_511) | r1_tarski(k3_xboole_0(A_510, B_511), B_512))), inference(resolution, [status(thm)], [c_12, c_425])).
% 36.42/25.59  tff(c_12362, plain, (![A_513, B_514]: (r1_tarski(k3_xboole_0(A_513, B_514), B_514))), inference(resolution, [status(thm)], [c_12221, c_10])).
% 36.42/25.59  tff(c_14460, plain, (![A_563, B_564]: (k3_xboole_0(k3_xboole_0(A_563, B_564), B_564)=k3_xboole_0(A_563, B_564))), inference(resolution, [status(thm)], [c_12362, c_72])).
% 36.42/25.59  tff(c_14876, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_14460])).
% 36.42/25.59  tff(c_57105, plain, (![A_1245, A_1244]: (k3_xboole_0(k4_xboole_0(A_1245, A_1244), A_1244)=k3_xboole_0(k1_xboole_0, A_1244))), inference(superposition, [status(thm), theory('equality')], [c_56603, c_14876])).
% 36.42/25.59  tff(c_57713, plain, (![A_1250, A_1251]: (k3_xboole_0(k4_xboole_0(A_1250, A_1251), A_1251)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_199, c_57105])).
% 36.42/25.59  tff(c_4258, plain, (![A_305, D_306]: (k2_zfmisc_1(k3_xboole_0(A_305, '#skF_11'), k3_xboole_0('#skF_12', D_306))=k2_zfmisc_1(k3_xboole_0('#skF_13', A_305), k3_xboole_0('#skF_14', D_306)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1609])).
% 36.42/25.59  tff(c_4374, plain, (![A_305]: (k2_zfmisc_1(k3_xboole_0(A_305, '#skF_11'), k3_xboole_0('#skF_12', '#skF_14'))=k2_zfmisc_1(k3_xboole_0('#skF_13', A_305), '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_4258])).
% 36.42/25.59  tff(c_57847, plain, (![A_1250]: (k2_zfmisc_1(k3_xboole_0('#skF_13', k4_xboole_0(A_1250, '#skF_11')), '#skF_14')=k2_zfmisc_1(k1_xboole_0, k3_xboole_0('#skF_12', '#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_57713, c_4374])).
% 36.42/25.59  tff(c_70639, plain, (![A_1336]: (k2_zfmisc_1(k3_xboole_0('#skF_13', k4_xboole_0(A_1336, '#skF_11')), '#skF_14')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_57847])).
% 36.42/25.59  tff(c_70662, plain, (k2_zfmisc_1(k4_xboole_0('#skF_13', '#skF_11'), '#skF_14')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11795, c_70639])).
% 36.42/25.59  tff(c_70736, plain, (k1_xboole_0='#skF_14' | k4_xboole_0('#skF_13', '#skF_11')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_70662, c_90])).
% 36.42/25.59  tff(c_70739, plain, (k4_xboole_0('#skF_13', '#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_70736])).
% 36.42/25.59  tff(c_71038, plain, (![D_23]: (r2_hidden(D_23, k1_xboole_0) | r2_hidden(D_23, '#skF_11') | ~r2_hidden(D_23, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_70739, c_32])).
% 36.42/25.59  tff(c_71146, plain, (![D_1337]: (r2_hidden(D_1337, '#skF_11') | ~r2_hidden(D_1337, '#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_1489, c_71038])).
% 36.42/25.59  tff(c_90984, plain, (![A_1528]: (r1_tarski(A_1528, '#skF_11') | ~r2_hidden('#skF_2'(A_1528, '#skF_11'), '#skF_13'))), inference(resolution, [status(thm)], [c_71146, c_10])).
% 36.42/25.59  tff(c_91016, plain, (r1_tarski('#skF_13', '#skF_11')), inference(resolution, [status(thm)], [c_12, c_90984])).
% 36.42/25.59  tff(c_91026, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77399, c_77399, c_91016])).
% 36.42/25.59  tff(c_91027, plain, (k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_70736])).
% 36.42/25.59  tff(c_92, plain, (![A_45]: (k2_zfmisc_1(A_45, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_121])).
% 36.42/25.59  tff(c_1636, plain, (![D_197]: (k2_zfmisc_1(k3_xboole_0('#skF_13', '#skF_11'), k3_xboole_0('#skF_14', D_197))=k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', D_197)))), inference(superposition, [status(thm), theory('equality')], [c_234, c_1609])).
% 36.42/25.59  tff(c_57326, plain, (![A_1245]: (k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', k4_xboole_0(A_1245, '#skF_14')))=k2_zfmisc_1(k3_xboole_0('#skF_13', '#skF_11'), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_56603, c_1636])).
% 36.42/25.59  tff(c_59017, plain, (![A_1254]: (k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', k4_xboole_0(A_1254, '#skF_14')))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_57326])).
% 36.42/25.59  tff(c_102, plain, (k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_134])).
% 36.42/25.59  tff(c_14311, plain, (![D_561, B_562]: (k3_xboole_0('#skF_12', D_561)=k1_xboole_0 | k3_xboole_0('#skF_11', B_562)=k1_xboole_0 | k2_zfmisc_1(k3_xboole_0('#skF_13', B_562), k3_xboole_0('#skF_14', D_561))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1609, c_90])).
% 36.42/25.59  tff(c_14389, plain, (![D_197]: (k3_xboole_0('#skF_12', D_197)=k1_xboole_0 | k3_xboole_0('#skF_11', '#skF_11')=k1_xboole_0 | k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', D_197))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1636, c_14311])).
% 36.42/25.59  tff(c_14451, plain, (![D_197]: (k3_xboole_0('#skF_12', D_197)=k1_xboole_0 | k1_xboole_0='#skF_11' | k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', D_197))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_234, c_14389])).
% 36.42/25.59  tff(c_14452, plain, (![D_197]: (k3_xboole_0('#skF_12', D_197)=k1_xboole_0 | k2_zfmisc_1('#skF_11', k3_xboole_0('#skF_12', D_197))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_102, c_14451])).
% 36.42/25.59  tff(c_59125, plain, (![A_1255]: (k3_xboole_0('#skF_12', k4_xboole_0(A_1255, '#skF_14'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_59017, c_14452])).
% 36.42/25.59  tff(c_59538, plain, (k4_xboole_0('#skF_12', '#skF_14')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_59125, c_11795])).
% 36.42/25.59  tff(c_60625, plain, (![D_23]: (r2_hidden(D_23, k1_xboole_0) | r2_hidden(D_23, '#skF_14') | ~r2_hidden(D_23, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_59538, c_32])).
% 36.42/25.59  tff(c_61524, plain, (![D_1261]: (r2_hidden(D_1261, '#skF_14') | ~r2_hidden(D_1261, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_1489, c_60625])).
% 36.42/25.59  tff(c_60, plain, (![A_26, B_27]: (r2_hidden('#skF_7'(A_26, B_27), A_26) | r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_84])).
% 36.42/25.59  tff(c_6994, plain, (![A_371, B_372, B_373]: (r2_hidden('#skF_7'(A_371, B_372), B_373) | ~r1_tarski(A_371, B_373) | r1_xboole_0(A_371, B_372))), inference(resolution, [status(thm)], [c_60, c_663])).
% 36.42/25.59  tff(c_7043, plain, (![A_374, B_375]: (~r1_tarski(A_374, k1_xboole_0) | r1_xboole_0(A_374, B_375))), inference(resolution, [status(thm)], [c_6994, c_1489])).
% 36.42/25.59  tff(c_56, plain, (![A_26, B_27, C_30]: (~r1_xboole_0(A_26, B_27) | ~r2_hidden(C_30, B_27) | ~r2_hidden(C_30, A_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 36.42/25.59  tff(c_7061, plain, (![C_379, B_380, A_381]: (~r2_hidden(C_379, B_380) | ~r2_hidden(C_379, A_381) | ~r1_tarski(A_381, k1_xboole_0))), inference(resolution, [status(thm)], [c_7043, c_56])).
% 36.42/25.59  tff(c_7142, plain, (![C_44, A_381]: (~r2_hidden(C_44, A_381) | ~r1_tarski(A_381, k1_xboole_0))), inference(resolution, [status(thm)], [c_80, c_7061])).
% 36.42/25.59  tff(c_61656, plain, (![D_1261]: (~r1_tarski('#skF_14', k1_xboole_0) | ~r2_hidden(D_1261, '#skF_12'))), inference(resolution, [status(thm)], [c_61524, c_7142])).
% 36.42/25.59  tff(c_61933, plain, (~r1_tarski('#skF_14', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_61656])).
% 36.42/25.59  tff(c_91346, plain, (~r1_tarski('#skF_14', '#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_91027, c_61933])).
% 36.42/25.59  tff(c_91480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_91346])).
% 36.42/25.59  tff(c_91483, plain, (![D_1533]: (~r2_hidden(D_1533, '#skF_12'))), inference(splitRight, [status(thm)], [c_61656])).
% 36.42/25.59  tff(c_91507, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_55726, c_91483])).
% 36.42/25.59  tff(c_91801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_91507])).
% 36.42/25.59  tff(c_91802, plain, ('#skF_14'!='#skF_12'), inference(splitRight, [status(thm)], [c_98])).
% 36.42/25.59  tff(c_91844, plain, (![B_1538, A_1539]: (~r2_hidden(B_1538, A_1539) | ~v1_xboole_0(A_1539))), inference(cnfTransformation, [status(thm)], [f_33])).
% 36.42/25.59  tff(c_91848, plain, (![C_44]: (~v1_xboole_0(k1_tarski(C_44)))), inference(resolution, [status(thm)], [c_80, c_91844])).
% 36.42/25.59  tff(c_91859, plain, (![C_1542, A_1543]: (C_1542=A_1543 | ~r2_hidden(C_1542, k1_tarski(A_1543)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 36.42/25.59  tff(c_91863, plain, (![A_1543]: ('#skF_1'(k1_tarski(A_1543))=A_1543 | v1_xboole_0(k1_tarski(A_1543)))), inference(resolution, [status(thm)], [c_6, c_91859])).
% 36.42/25.59  tff(c_91869, plain, (![A_1543]: ('#skF_1'(k1_tarski(A_1543))=A_1543)), inference(negUnitSimplification, [status(thm)], [c_91848, c_91863])).
% 36.42/25.59  tff(c_92380, plain, (![C_1609, B_1610, A_1611]: (r2_hidden(C_1609, B_1610) | ~r2_hidden(C_1609, A_1611) | ~r1_tarski(A_1611, B_1610))), inference(cnfTransformation, [status(thm)], [f_40])).
% 36.42/25.59  tff(c_92572, plain, (![A_1630, B_1631]: (r2_hidden('#skF_1'(A_1630), B_1631) | ~r1_tarski(A_1630, B_1631) | v1_xboole_0(A_1630))), inference(resolution, [status(thm)], [c_6, c_92380])).
% 36.42/25.59  tff(c_92329, plain, (![A_1602, B_1603, C_1604]: (~r1_xboole_0(A_1602, B_1603) | ~r2_hidden(C_1604, B_1603) | ~r2_hidden(C_1604, A_1602))), inference(cnfTransformation, [status(thm)], [f_84])).
% 36.42/25.59  tff(c_92338, plain, (![C_1604, A_39]: (~r2_hidden(C_1604, k1_xboole_0) | ~r2_hidden(C_1604, A_39))), inference(resolution, [status(thm)], [c_76, c_92329])).
% 36.42/25.59  tff(c_92970, plain, (![A_1659, A_1660]: (~r2_hidden('#skF_1'(A_1659), A_1660) | ~r1_tarski(A_1659, k1_xboole_0) | v1_xboole_0(A_1659))), inference(resolution, [status(thm)], [c_92572, c_92338])).
% 36.42/25.59  tff(c_92984, plain, (![A_1543, A_1660]: (~r2_hidden(A_1543, A_1660) | ~r1_tarski(k1_tarski(A_1543), k1_xboole_0) | v1_xboole_0(k1_tarski(A_1543)))), inference(superposition, [status(thm), theory('equality')], [c_91869, c_92970])).
% 36.42/25.59  tff(c_93070, plain, (![A_1666, A_1667]: (~r2_hidden(A_1666, A_1667) | ~r1_tarski(k1_tarski(A_1666), k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_91848, c_92984])).
% 36.42/25.59  tff(c_93103, plain, (![C_44]: (~r1_tarski(k1_tarski(C_44), k1_xboole_0))), inference(resolution, [status(thm)], [c_80, c_93070])).
% 36.42/25.59  tff(c_92066, plain, (![A_1567, B_1568]: (r2_hidden('#skF_2'(A_1567, B_1568), A_1567) | r1_tarski(A_1567, B_1568))), inference(cnfTransformation, [status(thm)], [f_40])).
% 36.42/25.59  tff(c_92084, plain, (![A_40, B_1568]: ('#skF_2'(k1_tarski(A_40), B_1568)=A_40 | r1_tarski(k1_tarski(A_40), B_1568))), inference(resolution, [status(thm)], [c_92066, c_78])).
% 36.42/25.59  tff(c_92997, plain, (![A_1661]: (~r1_tarski(A_1661, k1_xboole_0) | v1_xboole_0(A_1661))), inference(resolution, [status(thm)], [c_6, c_92970])).
% 36.42/25.59  tff(c_93001, plain, (![A_40]: (v1_xboole_0(k1_tarski(A_40)) | '#skF_2'(k1_tarski(A_40), k1_xboole_0)=A_40)), inference(resolution, [status(thm)], [c_92084, c_92997])).
% 36.42/25.59  tff(c_93032, plain, (![A_1665]: ('#skF_2'(k1_tarski(A_1665), k1_xboole_0)=A_1665)), inference(negUnitSimplification, [status(thm)], [c_91848, c_93001])).
% 36.42/25.59  tff(c_93044, plain, (![A_1665]: (~r2_hidden(A_1665, k1_xboole_0) | r1_tarski(k1_tarski(A_1665), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_93032, c_10])).
% 36.42/25.59  tff(c_93171, plain, (![A_1665]: (~r2_hidden(A_1665, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_93103, c_93044])).
% 36.42/25.59  tff(c_91887, plain, (![B_1547, A_1548]: (k3_xboole_0(B_1547, A_1548)=k3_xboole_0(A_1548, B_1547))), inference(cnfTransformation, [status(thm)], [f_27])).
% 36.42/25.59  tff(c_91903, plain, (![A_1548]: (k3_xboole_0(k1_xboole_0, A_1548)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_91887, c_74])).
% 36.42/25.59  tff(c_93796, plain, (![A_1704, B_1705, C_1706]: (r2_hidden('#skF_3'(A_1704, B_1705, C_1706), A_1704) | r2_hidden('#skF_4'(A_1704, B_1705, C_1706), C_1706) | k3_xboole_0(A_1704, B_1705)=C_1706)), inference(cnfTransformation, [status(thm)], [f_49])).
% 36.42/25.59  tff(c_143145, plain, (![A_2700, B_2701, A_2702, B_2703]: (r2_hidden('#skF_4'(A_2700, B_2701, k3_xboole_0(A_2702, B_2703)), A_2702) | r2_hidden('#skF_3'(A_2700, B_2701, k3_xboole_0(A_2702, B_2703)), A_2700) | k3_xboole_0(A_2702, B_2703)=k3_xboole_0(A_2700, B_2701))), inference(resolution, [status(thm)], [c_93796, c_18])).
% 36.42/25.59  tff(c_143434, plain, (![A_2700, B_2701, A_1548]: (r2_hidden('#skF_4'(A_2700, B_2701, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_3'(A_2700, B_2701, k3_xboole_0(k1_xboole_0, A_1548)), A_2700) | k3_xboole_0(k1_xboole_0, A_1548)=k3_xboole_0(A_2700, B_2701))), inference(superposition, [status(thm), theory('equality')], [c_91903, c_143145])).
% 36.42/25.59  tff(c_143513, plain, (![A_2700, B_2701]: (r2_hidden('#skF_4'(A_2700, B_2701, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_3'(A_2700, B_2701, k1_xboole_0), A_2700) | k3_xboole_0(A_2700, B_2701)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_91903, c_91903, c_143434])).
% 36.42/25.59  tff(c_147053, plain, (![A_2764, B_2765]: (r2_hidden('#skF_3'(A_2764, B_2765, k1_xboole_0), A_2764) | k3_xboole_0(A_2764, B_2765)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_93171, c_143513])).
% 36.42/25.59  tff(c_93278, plain, (![A_1676, B_1677, C_1678]: (r2_hidden('#skF_3'(A_1676, B_1677, C_1678), B_1677) | r2_hidden('#skF_4'(A_1676, B_1677, C_1678), C_1678) | k3_xboole_0(A_1676, B_1677)=C_1678)), inference(cnfTransformation, [status(thm)], [f_49])).
% 36.42/25.59  tff(c_93338, plain, (![A_1676, A_18, B_19, C_1678]: (~r2_hidden('#skF_3'(A_1676, k4_xboole_0(A_18, B_19), C_1678), B_19) | r2_hidden('#skF_4'(A_1676, k4_xboole_0(A_18, B_19), C_1678), C_1678) | k3_xboole_0(A_1676, k4_xboole_0(A_18, B_19))=C_1678)), inference(resolution, [status(thm)], [c_93278, c_34])).
% 36.42/25.59  tff(c_147056, plain, (![A_2764, A_18]: (r2_hidden('#skF_4'(A_2764, k4_xboole_0(A_18, A_2764), k1_xboole_0), k1_xboole_0) | k3_xboole_0(A_2764, k4_xboole_0(A_18, A_2764))=k1_xboole_0)), inference(resolution, [status(thm)], [c_147053, c_93338])).
% 36.42/25.59  tff(c_147123, plain, (![A_2766, A_2767]: (k3_xboole_0(A_2766, k4_xboole_0(A_2767, A_2766))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_93171, c_147056])).
% 36.42/25.59  tff(c_91803, plain, ('#skF_11'='#skF_13'), inference(splitRight, [status(thm)], [c_98])).
% 36.42/25.59  tff(c_91809, plain, (k1_xboole_0!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_91803, c_102])).
% 36.42/25.59  tff(c_91967, plain, (![A_1550, B_1551]: (k3_xboole_0(A_1550, B_1551)=A_1550 | ~r1_tarski(A_1550, B_1551))), inference(cnfTransformation, [status(thm)], [f_104])).
% 36.42/25.59  tff(c_91971, plain, (![B_35]: (k3_xboole_0(B_35, B_35)=B_35)), inference(resolution, [status(thm)], [c_70, c_91967])).
% 36.42/25.59  tff(c_91808, plain, (k2_zfmisc_1('#skF_13', '#skF_14')=k2_zfmisc_1('#skF_13', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_91803, c_104])).
% 36.42/25.59  tff(c_92901, plain, (![A_1653, C_1654, B_1655, D_1656]: (k3_xboole_0(k2_zfmisc_1(A_1653, C_1654), k2_zfmisc_1(B_1655, D_1656))=k2_zfmisc_1(k3_xboole_0(A_1653, B_1655), k3_xboole_0(C_1654, D_1656)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 36.42/25.59  tff(c_92939, plain, (![B_1655, D_1656]: (k3_xboole_0(k2_zfmisc_1('#skF_13', '#skF_12'), k2_zfmisc_1(B_1655, D_1656))=k2_zfmisc_1(k3_xboole_0('#skF_13', B_1655), k3_xboole_0('#skF_14', D_1656)))), inference(superposition, [status(thm), theory('equality')], [c_91808, c_92901])).
% 36.42/25.59  tff(c_93350, plain, (![B_1679, D_1680]: (k2_zfmisc_1(k3_xboole_0('#skF_13', B_1679), k3_xboole_0('#skF_14', D_1680))=k2_zfmisc_1(k3_xboole_0('#skF_13', B_1679), k3_xboole_0('#skF_12', D_1680)))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92939])).
% 36.42/25.59  tff(c_93377, plain, (![D_1680]: (k2_zfmisc_1(k3_xboole_0('#skF_13', '#skF_13'), k3_xboole_0('#skF_12', D_1680))=k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_14', D_1680)))), inference(superposition, [status(thm), theory('equality')], [c_91971, c_93350])).
% 36.42/25.59  tff(c_96515, plain, (![D_1798]: (k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_14', D_1798))=k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_12', D_1798)))), inference(demodulation, [status(thm), theory('equality')], [c_91971, c_93377])).
% 36.42/25.59  tff(c_96527, plain, (![D_1798]: (k3_xboole_0('#skF_14', D_1798)=k1_xboole_0 | k1_xboole_0='#skF_13' | k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_12', D_1798))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_96515, c_90])).
% 36.42/25.59  tff(c_96562, plain, (![D_1798]: (k3_xboole_0('#skF_14', D_1798)=k1_xboole_0 | k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_12', D_1798))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_91809, c_96527])).
% 36.42/25.59  tff(c_147794, plain, (![A_2767]: (k3_xboole_0('#skF_14', k4_xboole_0(A_2767, '#skF_12'))=k1_xboole_0 | k2_zfmisc_1('#skF_13', k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_147123, c_96562])).
% 36.42/25.59  tff(c_148235, plain, (![A_2768]: (k3_xboole_0('#skF_14', k4_xboole_0(A_2768, '#skF_12'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_147794])).
% 36.42/25.59  tff(c_36, plain, (![D_23, A_18, B_19]: (r2_hidden(D_23, A_18) | ~r2_hidden(D_23, k4_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 36.42/25.59  tff(c_112773, plain, (![A_2125, B_2126, B_2127]: (r2_hidden('#skF_2'(k4_xboole_0(A_2125, B_2126), B_2127), A_2125) | r1_tarski(k4_xboole_0(A_2125, B_2126), B_2127))), inference(resolution, [status(thm)], [c_92066, c_36])).
% 36.42/25.59  tff(c_112851, plain, (![A_2128, B_2129]: (r1_tarski(k4_xboole_0(A_2128, B_2129), A_2128))), inference(resolution, [status(thm)], [c_112773, c_10])).
% 36.42/25.59  tff(c_113189, plain, (![A_2138, B_2139]: (k3_xboole_0(k4_xboole_0(A_2138, B_2139), A_2138)=k4_xboole_0(A_2138, B_2139))), inference(resolution, [status(thm)], [c_112851, c_72])).
% 36.42/25.59  tff(c_113541, plain, (![A_2138, B_2139]: (k3_xboole_0(A_2138, k4_xboole_0(A_2138, B_2139))=k4_xboole_0(A_2138, B_2139))), inference(superposition, [status(thm), theory('equality')], [c_113189, c_2])).
% 36.42/25.59  tff(c_148554, plain, (k4_xboole_0('#skF_14', '#skF_12')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_148235, c_113541])).
% 36.42/25.59  tff(c_149420, plain, (![D_23]: (r2_hidden(D_23, k1_xboole_0) | r2_hidden(D_23, '#skF_12') | ~r2_hidden(D_23, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_148554, c_32])).
% 36.42/25.59  tff(c_151756, plain, (![D_2777]: (r2_hidden(D_2777, '#skF_12') | ~r2_hidden(D_2777, '#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_93171, c_149420])).
% 36.42/25.59  tff(c_159300, plain, (![B_2846]: (r2_hidden('#skF_2'('#skF_14', B_2846), '#skF_12') | r1_tarski('#skF_14', B_2846))), inference(resolution, [status(thm)], [c_12, c_151756])).
% 36.42/25.59  tff(c_159323, plain, (r1_tarski('#skF_14', '#skF_12')), inference(resolution, [status(thm)], [c_159300, c_10])).
% 36.42/25.59  tff(c_50, plain, (![A_24, B_25]: (r2_xboole_0(A_24, B_25) | B_25=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_66])).
% 36.42/25.59  tff(c_64, plain, (![A_31, B_32]: (r2_hidden('#skF_8'(A_31, B_32), B_32) | ~r2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_94])).
% 36.42/25.59  tff(c_93412, plain, (![D_1680]: (k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_14', D_1680))=k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_12', D_1680)))), inference(demodulation, [status(thm), theory('equality')], [c_91971, c_93377])).
% 36.42/25.59  tff(c_147804, plain, (![A_2767]: (k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_12', k4_xboole_0(A_2767, '#skF_14')))=k2_zfmisc_1('#skF_13', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_147123, c_93412])).
% 36.42/25.59  tff(c_154275, plain, (![A_2807]: (k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_12', k4_xboole_0(A_2807, '#skF_14')))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_147804])).
% 36.42/25.59  tff(c_92942, plain, (![A_1653, C_1654]: (k3_xboole_0(k2_zfmisc_1(A_1653, C_1654), k2_zfmisc_1('#skF_13', '#skF_12'))=k2_zfmisc_1(k3_xboole_0(A_1653, '#skF_13'), k3_xboole_0(C_1654, '#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_91808, c_92901])).
% 36.42/25.59  tff(c_93115, plain, (![A_1669, C_1670]: (k2_zfmisc_1(k3_xboole_0(A_1669, '#skF_13'), k3_xboole_0(C_1670, '#skF_14'))=k2_zfmisc_1(k3_xboole_0(A_1669, '#skF_13'), k3_xboole_0(C_1670, '#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92942])).
% 36.42/25.59  tff(c_93134, plain, (![C_1670]: (k2_zfmisc_1(k3_xboole_0('#skF_13', '#skF_13'), k3_xboole_0(C_1670, '#skF_12'))=k2_zfmisc_1('#skF_13', k3_xboole_0(C_1670, '#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_91971, c_93115])).
% 36.42/25.59  tff(c_96723, plain, (![C_1805]: (k2_zfmisc_1('#skF_13', k3_xboole_0(C_1805, '#skF_14'))=k2_zfmisc_1('#skF_13', k3_xboole_0(C_1805, '#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_91971, c_93134])).
% 36.42/25.59  tff(c_96922, plain, (![B_1809]: (k2_zfmisc_1('#skF_13', k3_xboole_0(B_1809, '#skF_12'))=k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_14', B_1809)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_96723])).
% 36.42/25.59  tff(c_96953, plain, (![B_1809]: (k3_xboole_0(B_1809, '#skF_12')=k1_xboole_0 | k1_xboole_0='#skF_13' | k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_14', B_1809))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_96922, c_90])).
% 36.42/25.59  tff(c_97009, plain, (![B_1809]: (k3_xboole_0(B_1809, '#skF_12')=k1_xboole_0 | k1_xboole_0='#skF_13' | k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_12', B_1809))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_93412, c_96953])).
% 36.42/25.59  tff(c_97010, plain, (![B_1809]: (k3_xboole_0(B_1809, '#skF_12')=k1_xboole_0 | k2_zfmisc_1('#skF_13', k3_xboole_0('#skF_12', B_1809))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_91809, c_97009])).
% 36.42/25.59  tff(c_154366, plain, (![A_2808]: (k3_xboole_0(k4_xboole_0(A_2808, '#skF_14'), '#skF_12')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_154275, c_97010])).
% 36.42/25.59  tff(c_112977, plain, (![A_2128, B_2129]: (k3_xboole_0(k4_xboole_0(A_2128, B_2129), A_2128)=k4_xboole_0(A_2128, B_2129))), inference(resolution, [status(thm)], [c_112851, c_72])).
% 36.42/25.59  tff(c_154718, plain, (k4_xboole_0('#skF_12', '#skF_14')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_154366, c_112977])).
% 36.42/25.59  tff(c_155536, plain, (![D_23]: (r2_hidden(D_23, k1_xboole_0) | r2_hidden(D_23, '#skF_14') | ~r2_hidden(D_23, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_154718, c_32])).
% 36.42/25.59  tff(c_156782, plain, (![D_2816]: (r2_hidden(D_2816, '#skF_14') | ~r2_hidden(D_2816, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_93171, c_155536])).
% 36.42/25.59  tff(c_62, plain, (![A_31, B_32]: (~r2_hidden('#skF_8'(A_31, B_32), A_31) | ~r2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_94])).
% 36.42/25.59  tff(c_161853, plain, (![B_2862]: (~r2_xboole_0('#skF_14', B_2862) | ~r2_hidden('#skF_8'('#skF_14', B_2862), '#skF_12'))), inference(resolution, [status(thm)], [c_156782, c_62])).
% 36.42/25.59  tff(c_161883, plain, (~r2_xboole_0('#skF_14', '#skF_12')), inference(resolution, [status(thm)], [c_64, c_161853])).
% 36.42/25.59  tff(c_162233, plain, ('#skF_14'='#skF_12' | ~r1_tarski('#skF_14', '#skF_12')), inference(resolution, [status(thm)], [c_50, c_161883])).
% 36.42/25.59  tff(c_162236, plain, ('#skF_14'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_159323, c_162233])).
% 36.42/25.59  tff(c_162238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91802, c_162236])).
% 36.42/25.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.42/25.59  
% 36.42/25.59  Inference rules
% 36.42/25.59  ----------------------
% 36.42/25.59  #Ref     : 0
% 36.42/25.59  #Sup     : 40880
% 36.42/25.59  #Fact    : 0
% 36.42/25.59  #Define  : 0
% 36.42/25.59  #Split   : 23
% 36.42/25.59  #Chain   : 0
% 36.42/25.59  #Close   : 0
% 36.42/25.59  
% 36.42/25.59  Ordering : KBO
% 36.42/25.59  
% 36.42/25.59  Simplification rules
% 36.42/25.59  ----------------------
% 36.42/25.59  #Subsume      : 15311
% 36.42/25.59  #Demod        : 30878
% 36.42/25.59  #Tautology    : 10337
% 36.42/25.59  #SimpNegUnit  : 724
% 36.42/25.59  #BackRed      : 730
% 36.42/25.59  
% 36.42/25.59  #Partial instantiations: 0
% 36.42/25.59  #Strategies tried      : 1
% 36.42/25.59  
% 36.42/25.59  Timing (in seconds)
% 36.42/25.59  ----------------------
% 36.42/25.59  Preprocessing        : 0.36
% 36.42/25.59  Parsing              : 0.18
% 36.42/25.59  CNF conversion       : 0.03
% 36.42/25.59  Main loop            : 24.42
% 36.42/25.59  Inferencing          : 3.61
% 36.42/25.59  Reduction            : 10.27
% 36.42/25.59  Demodulation         : 8.50
% 36.42/25.59  BG Simplification    : 0.38
% 36.42/25.59  Subsumption          : 8.41
% 36.42/25.59  Abstraction          : 0.59
% 36.42/25.59  MUC search           : 0.00
% 36.42/25.59  Cooper               : 0.00
% 36.42/25.59  Total                : 24.86
% 36.42/25.59  Index Insertion      : 0.00
% 36.42/25.59  Index Deletion       : 0.00
% 36.42/25.59  Index Matching       : 0.00
% 36.42/25.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
