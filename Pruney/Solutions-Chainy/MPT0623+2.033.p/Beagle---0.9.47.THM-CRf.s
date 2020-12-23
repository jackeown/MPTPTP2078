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
% DateTime   : Thu Dec  3 10:03:10 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 329 expanded)
%              Number of leaves         :   41 ( 123 expanded)
%              Depth                    :   15
%              Number of atoms          :  194 ( 814 expanded)
%              Number of equality atoms :  105 ( 470 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_104,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_79,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_67,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_91,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_84,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_110,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_26,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1310,plain,(
    ! [A_198,B_199,C_200] :
      ( r2_hidden('#skF_2'(A_198,B_199,C_200),B_199)
      | r2_hidden('#skF_3'(A_198,B_199,C_200),C_200)
      | k3_xboole_0(A_198,B_199) = C_200 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [A_21] : k2_zfmisc_1(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_143,plain,(
    ! [A_52,B_53] : ~ r2_hidden(A_52,k2_zfmisc_1(A_52,B_53)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_146,plain,(
    ! [A_21] : ~ r2_hidden(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_143])).

tff(c_1335,plain,(
    ! [A_198,C_200] :
      ( r2_hidden('#skF_3'(A_198,k1_xboole_0,C_200),C_200)
      | k3_xboole_0(A_198,k1_xboole_0) = C_200 ) ),
    inference(resolution,[status(thm)],[c_1310,c_146])).

tff(c_1362,plain,(
    ! [A_198,C_200] :
      ( r2_hidden('#skF_3'(A_198,k1_xboole_0,C_200),C_200)
      | k1_xboole_0 = C_200 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1335])).

tff(c_76,plain,(
    ! [A_35,B_39] :
      ( k1_relat_1('#skF_7'(A_35,B_39)) = A_35
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_78,plain,(
    ! [A_35,B_39] :
      ( v1_funct_1('#skF_7'(A_35,B_39))
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_80,plain,(
    ! [A_35,B_39] :
      ( v1_relat_1('#skF_7'(A_35,B_39))
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_390,plain,(
    ! [A_93,B_94] :
      ( r2_hidden('#skF_1'(A_93,B_94),A_93)
      | r1_tarski(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [C_18,A_14] :
      ( C_18 = A_14
      | ~ r2_hidden(C_18,k1_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_404,plain,(
    ! [A_14,B_94] :
      ( '#skF_1'(k1_tarski(A_14),B_94) = A_14
      | r1_tarski(k1_tarski(A_14),B_94) ) ),
    inference(resolution,[status(thm)],[c_390,c_30])).

tff(c_424,plain,(
    ! [A_100,B_101] :
      ( k2_relat_1('#skF_7'(A_100,B_101)) = k1_tarski(B_101)
      | k1_xboole_0 = A_100 ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_82,plain,(
    ! [C_42] :
      ( ~ r1_tarski(k2_relat_1(C_42),'#skF_8')
      | k1_relat_1(C_42) != '#skF_9'
      | ~ v1_funct_1(C_42)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_517,plain,(
    ! [B_120,A_121] :
      ( ~ r1_tarski(k1_tarski(B_120),'#skF_8')
      | k1_relat_1('#skF_7'(A_121,B_120)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_121,B_120))
      | ~ v1_relat_1('#skF_7'(A_121,B_120))
      | k1_xboole_0 = A_121 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_82])).

tff(c_764,plain,(
    ! [A_138,A_139] :
      ( k1_relat_1('#skF_7'(A_138,A_139)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_138,A_139))
      | ~ v1_relat_1('#skF_7'(A_138,A_139))
      | k1_xboole_0 = A_138
      | '#skF_1'(k1_tarski(A_139),'#skF_8') = A_139 ) ),
    inference(resolution,[status(thm)],[c_404,c_517])).

tff(c_1005,plain,(
    ! [A_167,B_168] :
      ( k1_relat_1('#skF_7'(A_167,B_168)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_167,B_168))
      | '#skF_1'(k1_tarski(B_168),'#skF_8') = B_168
      | k1_xboole_0 = A_167 ) ),
    inference(resolution,[status(thm)],[c_80,c_764])).

tff(c_1063,plain,(
    ! [A_174,B_175] :
      ( k1_relat_1('#skF_7'(A_174,B_175)) != '#skF_9'
      | '#skF_1'(k1_tarski(B_175),'#skF_8') = B_175
      | k1_xboole_0 = A_174 ) ),
    inference(resolution,[status(thm)],[c_78,c_1005])).

tff(c_1066,plain,(
    ! [A_35,B_39] :
      ( A_35 != '#skF_9'
      | '#skF_1'(k1_tarski(B_39),'#skF_8') = B_39
      | k1_xboole_0 = A_35
      | k1_xboole_0 = A_35 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_1063])).

tff(c_1068,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1066])).

tff(c_64,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_54,plain,(
    ! [A_27] : v1_relat_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_90,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_54])).

tff(c_58,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_152,plain,(
    ! [C_57] :
      ( ~ r1_tarski(k2_relat_1(C_57),'#skF_8')
      | k1_relat_1(C_57) != '#skF_9'
      | ~ v1_funct_1(C_57)
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_155,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_8')
    | k1_relat_1(k1_xboole_0) != '#skF_9'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_152])).

tff(c_157,plain,
    ( k1_xboole_0 != '#skF_9'
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_58,c_28,c_155])).

tff(c_158,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_68,plain,(
    ! [A_29] : k1_relat_1('#skF_6'(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_72,plain,(
    ! [A_29] : v1_relat_1('#skF_6'(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_194,plain,(
    ! [A_68] :
      ( k1_relat_1(A_68) != k1_xboole_0
      | k1_xboole_0 = A_68
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_206,plain,(
    ! [A_29] :
      ( k1_relat_1('#skF_6'(A_29)) != k1_xboole_0
      | '#skF_6'(A_29) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_72,c_194])).

tff(c_216,plain,(
    ! [A_69] :
      ( k1_xboole_0 != A_69
      | '#skF_6'(A_69) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_206])).

tff(c_70,plain,(
    ! [A_29] : v1_funct_1('#skF_6'(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_224,plain,(
    ! [A_69] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_69 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_70])).

tff(c_232,plain,(
    ! [A_69] : k1_xboole_0 != A_69 ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_224])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_46])).

tff(c_247,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_1108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1068,c_247])).

tff(c_1117,plain,(
    ! [B_179] : '#skF_1'(k1_tarski(B_179),'#skF_8') = B_179 ),
    inference(splitRight,[status(thm)],[c_1066])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1151,plain,(
    ! [B_180] :
      ( ~ r2_hidden(B_180,'#skF_8')
      | r1_tarski(k1_tarski(B_180),'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1117,c_4])).

tff(c_430,plain,(
    ! [B_101,A_100] :
      ( ~ r1_tarski(k1_tarski(B_101),'#skF_8')
      | k1_relat_1('#skF_7'(A_100,B_101)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_100,B_101))
      | ~ v1_relat_1('#skF_7'(A_100,B_101))
      | k1_xboole_0 = A_100 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_82])).

tff(c_1171,plain,(
    ! [A_183,B_184] :
      ( k1_relat_1('#skF_7'(A_183,B_184)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_183,B_184))
      | ~ v1_relat_1('#skF_7'(A_183,B_184))
      | k1_xboole_0 = A_183
      | ~ r2_hidden(B_184,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1151,c_430])).

tff(c_1445,plain,(
    ! [A_207,B_208] :
      ( k1_relat_1('#skF_7'(A_207,B_208)) != '#skF_9'
      | ~ v1_funct_1('#skF_7'(A_207,B_208))
      | ~ r2_hidden(B_208,'#skF_8')
      | k1_xboole_0 = A_207 ) ),
    inference(resolution,[status(thm)],[c_80,c_1171])).

tff(c_1450,plain,(
    ! [A_209,B_210] :
      ( k1_relat_1('#skF_7'(A_209,B_210)) != '#skF_9'
      | ~ r2_hidden(B_210,'#skF_8')
      | k1_xboole_0 = A_209 ) ),
    inference(resolution,[status(thm)],[c_78,c_1445])).

tff(c_1453,plain,(
    ! [A_35,B_39] :
      ( A_35 != '#skF_9'
      | ~ r2_hidden(B_39,'#skF_8')
      | k1_xboole_0 = A_35
      | k1_xboole_0 = A_35 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_1450])).

tff(c_1455,plain,(
    ! [B_211] : ~ r2_hidden(B_211,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1453])).

tff(c_1463,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1362,c_1455])).

tff(c_1498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_1463])).

tff(c_1500,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1453])).

tff(c_1542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1500,c_247])).

tff(c_1544,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_1543,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_1555,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1544,c_1543])).

tff(c_1549,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1543,c_90])).

tff(c_1564,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1555,c_1549])).

tff(c_1548,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1543,c_1543,c_58])).

tff(c_1565,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1555,c_1555,c_1548])).

tff(c_1547,plain,(
    ! [A_13] : r1_tarski('#skF_9',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1543,c_28])).

tff(c_1572,plain,(
    ! [A_13] : r1_tarski('#skF_8',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1555,c_1547])).

tff(c_1546,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1543,c_1543,c_56])).

tff(c_1582,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1555,c_1555,c_1546])).

tff(c_1570,plain,(
    ! [C_42] :
      ( ~ r1_tarski(k2_relat_1(C_42),'#skF_8')
      | k1_relat_1(C_42) != '#skF_8'
      | ~ v1_funct_1(C_42)
      | ~ v1_relat_1(C_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1555,c_82])).

tff(c_1586,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1582,c_1570])).

tff(c_1590,plain,(
    ~ v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1564,c_1565,c_1572,c_1586])).

tff(c_62,plain,(
    ! [A_28] :
      ( k1_relat_1(A_28) != k1_xboole_0
      | k1_xboole_0 = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1664,plain,(
    ! [A_230] :
      ( k1_relat_1(A_230) != '#skF_8'
      | A_230 = '#skF_8'
      | ~ v1_relat_1(A_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1544,c_1544,c_62])).

tff(c_1676,plain,(
    ! [A_29] :
      ( k1_relat_1('#skF_6'(A_29)) != '#skF_8'
      | '#skF_6'(A_29) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_72,c_1664])).

tff(c_1686,plain,(
    ! [A_231] :
      ( A_231 != '#skF_8'
      | '#skF_6'(A_231) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1676])).

tff(c_1694,plain,(
    ! [A_231] :
      ( v1_funct_1('#skF_8')
      | A_231 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1686,c_70])).

tff(c_1702,plain,(
    ! [A_231] : A_231 != '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1590,c_1694])).

tff(c_48,plain,(
    ! [B_22] : k2_zfmisc_1(k1_xboole_0,B_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1609,plain,(
    ! [B_22] : k2_zfmisc_1('#skF_8',B_22) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1544,c_1544,c_48])).

tff(c_1718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1702,c_1609])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:16:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.62  
% 3.52/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.63  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_4
% 3.52/1.63  
% 3.52/1.63  %Foreground sorts:
% 3.52/1.63  
% 3.52/1.63  
% 3.52/1.63  %Background operators:
% 3.52/1.63  
% 3.52/1.63  
% 3.52/1.63  %Foreground operators:
% 3.52/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.52/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.52/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.52/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.52/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.52/1.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.52/1.63  tff('#skF_9', type, '#skF_9': $i).
% 3.52/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.52/1.63  tff('#skF_8', type, '#skF_8': $i).
% 3.52/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.52/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.52/1.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.52/1.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.52/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.52/1.63  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.52/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.52/1.63  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.52/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.52/1.63  tff('#skF_6', type, '#skF_6': $i > $i).
% 3.52/1.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.52/1.63  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.52/1.63  
% 3.68/1.65  tff(f_122, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 3.68/1.65  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.68/1.65  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.68/1.65  tff(f_60, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.68/1.65  tff(f_63, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.68/1.65  tff(f_104, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 3.68/1.65  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.68/1.65  tff(f_52, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.68/1.65  tff(f_79, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 3.68/1.65  tff(f_67, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.68/1.65  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.68/1.65  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.68/1.65  tff(f_91, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 3.68/1.65  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.68/1.65  tff(c_84, plain, (k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.68/1.65  tff(c_110, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_84])).
% 3.68/1.65  tff(c_26, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.68/1.65  tff(c_1310, plain, (![A_198, B_199, C_200]: (r2_hidden('#skF_2'(A_198, B_199, C_200), B_199) | r2_hidden('#skF_3'(A_198, B_199, C_200), C_200) | k3_xboole_0(A_198, B_199)=C_200)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.68/1.65  tff(c_46, plain, (![A_21]: (k2_zfmisc_1(A_21, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.68/1.65  tff(c_143, plain, (![A_52, B_53]: (~r2_hidden(A_52, k2_zfmisc_1(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.68/1.65  tff(c_146, plain, (![A_21]: (~r2_hidden(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_143])).
% 3.68/1.65  tff(c_1335, plain, (![A_198, C_200]: (r2_hidden('#skF_3'(A_198, k1_xboole_0, C_200), C_200) | k3_xboole_0(A_198, k1_xboole_0)=C_200)), inference(resolution, [status(thm)], [c_1310, c_146])).
% 3.68/1.65  tff(c_1362, plain, (![A_198, C_200]: (r2_hidden('#skF_3'(A_198, k1_xboole_0, C_200), C_200) | k1_xboole_0=C_200)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1335])).
% 3.68/1.65  tff(c_76, plain, (![A_35, B_39]: (k1_relat_1('#skF_7'(A_35, B_39))=A_35 | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.68/1.65  tff(c_78, plain, (![A_35, B_39]: (v1_funct_1('#skF_7'(A_35, B_39)) | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.68/1.65  tff(c_80, plain, (![A_35, B_39]: (v1_relat_1('#skF_7'(A_35, B_39)) | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.68/1.65  tff(c_390, plain, (![A_93, B_94]: (r2_hidden('#skF_1'(A_93, B_94), A_93) | r1_tarski(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.68/1.65  tff(c_30, plain, (![C_18, A_14]: (C_18=A_14 | ~r2_hidden(C_18, k1_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.68/1.65  tff(c_404, plain, (![A_14, B_94]: ('#skF_1'(k1_tarski(A_14), B_94)=A_14 | r1_tarski(k1_tarski(A_14), B_94))), inference(resolution, [status(thm)], [c_390, c_30])).
% 3.68/1.65  tff(c_424, plain, (![A_100, B_101]: (k2_relat_1('#skF_7'(A_100, B_101))=k1_tarski(B_101) | k1_xboole_0=A_100)), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.68/1.65  tff(c_82, plain, (![C_42]: (~r1_tarski(k2_relat_1(C_42), '#skF_8') | k1_relat_1(C_42)!='#skF_9' | ~v1_funct_1(C_42) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.68/1.65  tff(c_517, plain, (![B_120, A_121]: (~r1_tarski(k1_tarski(B_120), '#skF_8') | k1_relat_1('#skF_7'(A_121, B_120))!='#skF_9' | ~v1_funct_1('#skF_7'(A_121, B_120)) | ~v1_relat_1('#skF_7'(A_121, B_120)) | k1_xboole_0=A_121)), inference(superposition, [status(thm), theory('equality')], [c_424, c_82])).
% 3.68/1.65  tff(c_764, plain, (![A_138, A_139]: (k1_relat_1('#skF_7'(A_138, A_139))!='#skF_9' | ~v1_funct_1('#skF_7'(A_138, A_139)) | ~v1_relat_1('#skF_7'(A_138, A_139)) | k1_xboole_0=A_138 | '#skF_1'(k1_tarski(A_139), '#skF_8')=A_139)), inference(resolution, [status(thm)], [c_404, c_517])).
% 3.68/1.65  tff(c_1005, plain, (![A_167, B_168]: (k1_relat_1('#skF_7'(A_167, B_168))!='#skF_9' | ~v1_funct_1('#skF_7'(A_167, B_168)) | '#skF_1'(k1_tarski(B_168), '#skF_8')=B_168 | k1_xboole_0=A_167)), inference(resolution, [status(thm)], [c_80, c_764])).
% 3.68/1.65  tff(c_1063, plain, (![A_174, B_175]: (k1_relat_1('#skF_7'(A_174, B_175))!='#skF_9' | '#skF_1'(k1_tarski(B_175), '#skF_8')=B_175 | k1_xboole_0=A_174)), inference(resolution, [status(thm)], [c_78, c_1005])).
% 3.68/1.65  tff(c_1066, plain, (![A_35, B_39]: (A_35!='#skF_9' | '#skF_1'(k1_tarski(B_39), '#skF_8')=B_39 | k1_xboole_0=A_35 | k1_xboole_0=A_35)), inference(superposition, [status(thm), theory('equality')], [c_76, c_1063])).
% 3.68/1.65  tff(c_1068, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_1066])).
% 3.68/1.65  tff(c_64, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.68/1.65  tff(c_54, plain, (![A_27]: (v1_relat_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.68/1.65  tff(c_90, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_64, c_54])).
% 3.68/1.65  tff(c_58, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.68/1.65  tff(c_28, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.68/1.65  tff(c_56, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.68/1.65  tff(c_152, plain, (![C_57]: (~r1_tarski(k2_relat_1(C_57), '#skF_8') | k1_relat_1(C_57)!='#skF_9' | ~v1_funct_1(C_57) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.68/1.65  tff(c_155, plain, (~r1_tarski(k1_xboole_0, '#skF_8') | k1_relat_1(k1_xboole_0)!='#skF_9' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_152])).
% 3.68/1.65  tff(c_157, plain, (k1_xboole_0!='#skF_9' | ~v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_58, c_28, c_155])).
% 3.68/1.65  tff(c_158, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_157])).
% 3.68/1.65  tff(c_68, plain, (![A_29]: (k1_relat_1('#skF_6'(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.68/1.65  tff(c_72, plain, (![A_29]: (v1_relat_1('#skF_6'(A_29)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.68/1.65  tff(c_194, plain, (![A_68]: (k1_relat_1(A_68)!=k1_xboole_0 | k1_xboole_0=A_68 | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.68/1.65  tff(c_206, plain, (![A_29]: (k1_relat_1('#skF_6'(A_29))!=k1_xboole_0 | '#skF_6'(A_29)=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_194])).
% 3.68/1.65  tff(c_216, plain, (![A_69]: (k1_xboole_0!=A_69 | '#skF_6'(A_69)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_206])).
% 3.68/1.65  tff(c_70, plain, (![A_29]: (v1_funct_1('#skF_6'(A_29)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.68/1.65  tff(c_224, plain, (![A_69]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_69)), inference(superposition, [status(thm), theory('equality')], [c_216, c_70])).
% 3.68/1.65  tff(c_232, plain, (![A_69]: (k1_xboole_0!=A_69)), inference(negUnitSimplification, [status(thm)], [c_158, c_224])).
% 3.68/1.65  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_232, c_46])).
% 3.68/1.65  tff(c_247, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_157])).
% 3.68/1.65  tff(c_1108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1068, c_247])).
% 3.68/1.65  tff(c_1117, plain, (![B_179]: ('#skF_1'(k1_tarski(B_179), '#skF_8')=B_179)), inference(splitRight, [status(thm)], [c_1066])).
% 3.68/1.65  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.68/1.65  tff(c_1151, plain, (![B_180]: (~r2_hidden(B_180, '#skF_8') | r1_tarski(k1_tarski(B_180), '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1117, c_4])).
% 3.68/1.65  tff(c_430, plain, (![B_101, A_100]: (~r1_tarski(k1_tarski(B_101), '#skF_8') | k1_relat_1('#skF_7'(A_100, B_101))!='#skF_9' | ~v1_funct_1('#skF_7'(A_100, B_101)) | ~v1_relat_1('#skF_7'(A_100, B_101)) | k1_xboole_0=A_100)), inference(superposition, [status(thm), theory('equality')], [c_424, c_82])).
% 3.68/1.65  tff(c_1171, plain, (![A_183, B_184]: (k1_relat_1('#skF_7'(A_183, B_184))!='#skF_9' | ~v1_funct_1('#skF_7'(A_183, B_184)) | ~v1_relat_1('#skF_7'(A_183, B_184)) | k1_xboole_0=A_183 | ~r2_hidden(B_184, '#skF_8'))), inference(resolution, [status(thm)], [c_1151, c_430])).
% 3.68/1.65  tff(c_1445, plain, (![A_207, B_208]: (k1_relat_1('#skF_7'(A_207, B_208))!='#skF_9' | ~v1_funct_1('#skF_7'(A_207, B_208)) | ~r2_hidden(B_208, '#skF_8') | k1_xboole_0=A_207)), inference(resolution, [status(thm)], [c_80, c_1171])).
% 3.68/1.65  tff(c_1450, plain, (![A_209, B_210]: (k1_relat_1('#skF_7'(A_209, B_210))!='#skF_9' | ~r2_hidden(B_210, '#skF_8') | k1_xboole_0=A_209)), inference(resolution, [status(thm)], [c_78, c_1445])).
% 3.68/1.65  tff(c_1453, plain, (![A_35, B_39]: (A_35!='#skF_9' | ~r2_hidden(B_39, '#skF_8') | k1_xboole_0=A_35 | k1_xboole_0=A_35)), inference(superposition, [status(thm), theory('equality')], [c_76, c_1450])).
% 3.68/1.65  tff(c_1455, plain, (![B_211]: (~r2_hidden(B_211, '#skF_8'))), inference(splitLeft, [status(thm)], [c_1453])).
% 3.68/1.65  tff(c_1463, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1362, c_1455])).
% 3.68/1.65  tff(c_1498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_1463])).
% 3.68/1.65  tff(c_1500, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_1453])).
% 3.68/1.65  tff(c_1542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1500, c_247])).
% 3.68/1.65  tff(c_1544, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_84])).
% 3.68/1.65  tff(c_1543, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_84])).
% 3.68/1.65  tff(c_1555, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1544, c_1543])).
% 3.68/1.65  tff(c_1549, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1543, c_90])).
% 3.68/1.65  tff(c_1564, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1555, c_1549])).
% 3.68/1.65  tff(c_1548, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1543, c_1543, c_58])).
% 3.68/1.65  tff(c_1565, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1555, c_1555, c_1548])).
% 3.68/1.65  tff(c_1547, plain, (![A_13]: (r1_tarski('#skF_9', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_1543, c_28])).
% 3.68/1.65  tff(c_1572, plain, (![A_13]: (r1_tarski('#skF_8', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_1555, c_1547])).
% 3.68/1.65  tff(c_1546, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1543, c_1543, c_56])).
% 3.68/1.65  tff(c_1582, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1555, c_1555, c_1546])).
% 3.68/1.65  tff(c_1570, plain, (![C_42]: (~r1_tarski(k2_relat_1(C_42), '#skF_8') | k1_relat_1(C_42)!='#skF_8' | ~v1_funct_1(C_42) | ~v1_relat_1(C_42))), inference(demodulation, [status(thm), theory('equality')], [c_1555, c_82])).
% 3.68/1.65  tff(c_1586, plain, (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_8')!='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1582, c_1570])).
% 3.68/1.65  tff(c_1590, plain, (~v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1564, c_1565, c_1572, c_1586])).
% 3.68/1.65  tff(c_62, plain, (![A_28]: (k1_relat_1(A_28)!=k1_xboole_0 | k1_xboole_0=A_28 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.68/1.65  tff(c_1664, plain, (![A_230]: (k1_relat_1(A_230)!='#skF_8' | A_230='#skF_8' | ~v1_relat_1(A_230))), inference(demodulation, [status(thm), theory('equality')], [c_1544, c_1544, c_62])).
% 3.68/1.65  tff(c_1676, plain, (![A_29]: (k1_relat_1('#skF_6'(A_29))!='#skF_8' | '#skF_6'(A_29)='#skF_8')), inference(resolution, [status(thm)], [c_72, c_1664])).
% 3.68/1.65  tff(c_1686, plain, (![A_231]: (A_231!='#skF_8' | '#skF_6'(A_231)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1676])).
% 3.68/1.65  tff(c_1694, plain, (![A_231]: (v1_funct_1('#skF_8') | A_231!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1686, c_70])).
% 3.68/1.65  tff(c_1702, plain, (![A_231]: (A_231!='#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1590, c_1694])).
% 3.68/1.65  tff(c_48, plain, (![B_22]: (k2_zfmisc_1(k1_xboole_0, B_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.68/1.65  tff(c_1609, plain, (![B_22]: (k2_zfmisc_1('#skF_8', B_22)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1544, c_1544, c_48])).
% 3.68/1.65  tff(c_1718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1702, c_1609])).
% 3.68/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.68/1.65  
% 3.68/1.65  Inference rules
% 3.68/1.65  ----------------------
% 3.68/1.65  #Ref     : 0
% 3.68/1.65  #Sup     : 338
% 3.68/1.65  #Fact    : 0
% 3.68/1.65  #Define  : 0
% 3.68/1.65  #Split   : 4
% 3.68/1.65  #Chain   : 0
% 3.68/1.65  #Close   : 0
% 3.68/1.65  
% 3.68/1.65  Ordering : KBO
% 3.68/1.65  
% 3.68/1.65  Simplification rules
% 3.68/1.65  ----------------------
% 3.68/1.65  #Subsume      : 52
% 3.68/1.65  #Demod        : 246
% 3.68/1.65  #Tautology    : 171
% 3.68/1.65  #SimpNegUnit  : 41
% 3.68/1.65  #BackRed      : 105
% 3.68/1.65  
% 3.68/1.65  #Partial instantiations: 0
% 3.68/1.65  #Strategies tried      : 1
% 3.68/1.65  
% 3.68/1.65  Timing (in seconds)
% 3.68/1.65  ----------------------
% 3.68/1.65  Preprocessing        : 0.34
% 3.68/1.65  Parsing              : 0.18
% 3.68/1.65  CNF conversion       : 0.03
% 3.68/1.65  Main loop            : 0.48
% 3.68/1.65  Inferencing          : 0.17
% 3.68/1.65  Reduction            : 0.15
% 3.68/1.65  Demodulation         : 0.10
% 3.68/1.65  BG Simplification    : 0.03
% 3.68/1.65  Subsumption          : 0.09
% 3.68/1.65  Abstraction          : 0.02
% 3.68/1.65  MUC search           : 0.00
% 3.68/1.65  Cooper               : 0.00
% 3.68/1.65  Total                : 0.85
% 3.68/1.65  Index Insertion      : 0.00
% 3.68/1.65  Index Deletion       : 0.00
% 3.68/1.65  Index Matching       : 0.00
% 3.68/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
