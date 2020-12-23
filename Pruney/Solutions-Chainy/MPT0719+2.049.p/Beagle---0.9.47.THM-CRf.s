%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:49 EST 2020

% Result     : Theorem 6.75s
% Output     : CNFRefutation 6.88s
% Verified   : 
% Statistics : Number of formulae       :  139 (1740 expanded)
%              Number of leaves         :   41 ( 609 expanded)
%              Depth                    :   26
%              Number of atoms          :  188 (2332 expanded)
%              Number of equality atoms :   68 (1065 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_129,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k4_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k5_xboole_0(B,C))
    <=> ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

tff(f_122,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_66,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_12,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_19,B_20] : r1_tarski(A_19,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_110,plain,(
    ! [A_77,B_78] :
      ( k3_xboole_0(A_77,B_78) = A_77
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_116,plain,(
    ! [A_80,B_81] : k3_xboole_0(A_80,k2_xboole_0(A_80,B_81)) = A_80 ),
    inference(resolution,[status(thm)],[c_20,c_110])).

tff(c_26,plain,(
    ! [A_26,B_27] : r1_xboole_0(k3_xboole_0(A_26,B_27),k4_xboole_0(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_122,plain,(
    ! [A_80,B_81] : r1_xboole_0(A_80,k4_xboole_0(A_80,k2_xboole_0(A_80,B_81))) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_26])).

tff(c_132,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | r1_xboole_0(A_84,k3_xboole_0(B_85,C_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_139,plain,(
    ! [A_87,A_88] :
      ( ~ r1_xboole_0(A_87,A_88)
      | r1_xboole_0(A_87,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_132])).

tff(c_149,plain,(
    ! [A_80] : r1_xboole_0(A_80,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_122,c_139])).

tff(c_160,plain,(
    ! [A_90,B_91] :
      ( k4_xboole_0(k2_xboole_0(A_90,B_91),B_91) = A_90
      | ~ r1_xboole_0(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_106,plain,(
    ! [A_75,B_76] : r1_xboole_0(k3_xboole_0(A_75,B_76),k4_xboole_0(A_75,B_76)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_109,plain,(
    ! [A_9] : r1_xboole_0(k1_xboole_0,k4_xboole_0(A_9,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_106])).

tff(c_167,plain,(
    ! [A_90] :
      ( r1_xboole_0(k1_xboole_0,A_90)
      | ~ r1_xboole_0(A_90,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_109])).

tff(c_180,plain,(
    ! [A_90] : r1_xboole_0(k1_xboole_0,A_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_167])).

tff(c_36,plain,(
    ! [A_34,B_35,C_36,D_37] :
      ( ~ r1_xboole_0(A_34,B_35)
      | r1_xboole_0(k2_zfmisc_1(A_34,C_36),k2_zfmisc_1(B_35,D_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_215,plain,(
    ! [A_112,B_113] : k2_xboole_0(k5_xboole_0(A_112,B_113),k3_xboole_0(A_112,B_113)) = k2_xboole_0(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_263,plain,(
    ! [A_119] : k2_xboole_0(k5_xboole_0(A_119,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_119,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_215])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(k2_xboole_0(A_24,B_25),B_25) = A_24
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_272,plain,(
    ! [A_119] :
      ( k4_xboole_0(k2_xboole_0(A_119,k1_xboole_0),k1_xboole_0) = k5_xboole_0(A_119,k1_xboole_0)
      | ~ r1_xboole_0(k5_xboole_0(A_119,k1_xboole_0),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_24])).

tff(c_290,plain,(
    ! [A_120] : k4_xboole_0(k2_xboole_0(A_120,k1_xboole_0),k1_xboole_0) = k5_xboole_0(A_120,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_272])).

tff(c_299,plain,(
    ! [A_120] :
      ( k5_xboole_0(A_120,k1_xboole_0) = A_120
      | ~ r1_xboole_0(A_120,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_24])).

tff(c_315,plain,(
    ! [A_120] : k5_xboole_0(A_120,k1_xboole_0) = A_120 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_299])).

tff(c_287,plain,(
    ! [A_119] : k4_xboole_0(k2_xboole_0(A_119,k1_xboole_0),k1_xboole_0) = k5_xboole_0(A_119,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_272])).

tff(c_321,plain,(
    ! [A_119] : k4_xboole_0(k2_xboole_0(A_119,k1_xboole_0),k1_xboole_0) = A_119 ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_287])).

tff(c_708,plain,(
    ! [A_165,B_166,C_167] : k4_xboole_0(k3_xboole_0(A_165,B_166),k3_xboole_0(C_167,B_166)) = k3_xboole_0(k4_xboole_0(A_165,C_167),B_166) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_756,plain,(
    ! [C_167,A_9] : k4_xboole_0(k1_xboole_0,k3_xboole_0(C_167,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(A_9,C_167),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_708])).

tff(c_762,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_756])).

tff(c_800,plain,(
    ! [A_169,B_170,C_171] : k2_xboole_0(k4_xboole_0(A_169,B_170),k3_xboole_0(A_169,C_171)) = k4_xboole_0(A_169,k4_xboole_0(B_170,C_171)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1070,plain,(
    ! [A_175,B_176,C_177] : r1_tarski(k4_xboole_0(A_175,B_176),k4_xboole_0(A_175,k4_xboole_0(B_176,C_177))) ),
    inference(superposition,[status(thm),theory(equality)],[c_800,c_20])).

tff(c_1156,plain,(
    ! [A_181] : r1_tarski(k4_xboole_0(A_181,k1_xboole_0),k4_xboole_0(A_181,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_1070])).

tff(c_1181,plain,(
    ! [A_24] :
      ( r1_tarski(A_24,k4_xboole_0(k2_xboole_0(A_24,k1_xboole_0),k1_xboole_0))
      | ~ r1_xboole_0(A_24,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1156])).

tff(c_1194,plain,(
    ! [A_24] : r1_tarski(A_24,A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_321,c_1181])).

tff(c_1544,plain,(
    ! [A_201,B_202] : k4_xboole_0(A_201,k4_xboole_0(B_202,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(A_201,B_202),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_800])).

tff(c_1653,plain,(
    ! [A_205] : k2_xboole_0(k4_xboole_0(A_205,k1_xboole_0),k1_xboole_0) = k4_xboole_0(A_205,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_1544])).

tff(c_1735,plain,(
    ! [A_24] :
      ( k4_xboole_0(k2_xboole_0(A_24,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_24,k1_xboole_0)
      | ~ r1_xboole_0(A_24,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1653])).

tff(c_1755,plain,(
    ! [A_24] : k2_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_321,c_1735])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski(k4_xboole_0(A_10,B_11),C_12)
      | ~ r1_tarski(A_10,k2_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1728,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_1653])).

tff(c_1752,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_1728])).

tff(c_323,plain,(
    ! [A_121] : k5_xboole_0(A_121,k1_xboole_0) = A_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_299])).

tff(c_6,plain,(
    ! [A_1,B_2,C_3] :
      ( r1_tarski(A_1,k2_xboole_0(B_2,C_3))
      | ~ r1_tarski(A_1,k5_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_403,plain,(
    ! [A_124,A_125] :
      ( r1_tarski(A_124,k2_xboole_0(A_125,k1_xboole_0))
      | ~ r1_tarski(A_124,A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_6])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_407,plain,(
    ! [A_124,A_125] :
      ( k3_xboole_0(A_124,k2_xboole_0(A_125,k1_xboole_0)) = A_124
      | ~ r1_tarski(A_124,A_125) ) ),
    inference(resolution,[status(thm)],[c_403,c_10])).

tff(c_1874,plain,(
    ! [A_124] :
      ( k3_xboole_0(A_124,k1_xboole_0) = A_124
      | ~ r1_tarski(A_124,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1752,c_407])).

tff(c_2104,plain,(
    ! [A_212] :
      ( k1_xboole_0 = A_212
      | ~ r1_tarski(A_212,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1874])).

tff(c_2124,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_tarski(A_10,k2_xboole_0(B_11,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_14,c_2104])).

tff(c_2407,plain,(
    ! [A_224,B_225] :
      ( k4_xboole_0(A_224,B_225) = k1_xboole_0
      | ~ r1_tarski(A_224,B_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1755,c_2124])).

tff(c_2444,plain,(
    ! [A_24] : k4_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1194,c_2407])).

tff(c_1198,plain,(
    ! [A_182] : r1_tarski(A_182,A_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_321,c_1181])).

tff(c_1219,plain,(
    ! [A_182] : k3_xboole_0(A_182,A_182) = A_182 ),
    inference(resolution,[status(thm)],[c_1198,c_10])).

tff(c_1942,plain,(
    ! [A_119] : k4_xboole_0(A_119,k1_xboole_0) = A_119 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1755,c_321])).

tff(c_770,plain,(
    ! [C_12] :
      ( r1_tarski(k1_xboole_0,C_12)
      | ~ r1_tarski(k1_xboole_0,k2_xboole_0(k1_xboole_0,C_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_14])).

tff(c_779,plain,(
    ! [C_12] : r1_tarski(k1_xboole_0,C_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_770])).

tff(c_2446,plain,(
    ! [C_12] : k4_xboole_0(k1_xboole_0,C_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_779,c_2407])).

tff(c_8055,plain,(
    ! [A_390,B_391,C_392] :
      ( k4_xboole_0(k2_xboole_0(A_390,B_391),k4_xboole_0(B_391,C_392)) = k2_xboole_0(A_390,k3_xboole_0(k2_xboole_0(A_390,B_391),C_392))
      | ~ r1_xboole_0(A_390,B_391) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_800])).

tff(c_8318,plain,(
    ! [A_24,C_392] :
      ( k2_xboole_0(A_24,k3_xboole_0(k2_xboole_0(A_24,k1_xboole_0),C_392)) = k4_xboole_0(A_24,k4_xboole_0(k1_xboole_0,C_392))
      | ~ r1_xboole_0(A_24,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1755,c_8055])).

tff(c_8401,plain,(
    ! [A_393,C_394] : k2_xboole_0(A_393,k3_xboole_0(A_393,C_394)) = A_393 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_1942,c_2446,c_1755,c_8318])).

tff(c_8549,plain,(
    ! [A_182] : k2_xboole_0(A_182,A_182) = A_182 ),
    inference(superposition,[status(thm),theory(equality)],[c_1219,c_8401])).

tff(c_1947,plain,(
    ! [A_208] : k2_xboole_0(A_208,k1_xboole_0) = A_208 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_321,c_1735])).

tff(c_114,plain,(
    ! [A_19,B_20] : k3_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = A_19 ),
    inference(resolution,[status(thm)],[c_20,c_110])).

tff(c_205,plain,(
    ! [A_102,B_103,C_104] :
      ( r1_xboole_0(A_102,k3_xboole_0(B_103,C_104))
      | ~ r1_tarski(A_102,k5_xboole_0(B_103,C_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_208,plain,(
    ! [A_102,A_19,B_20] :
      ( r1_xboole_0(A_102,A_19)
      | ~ r1_tarski(A_102,k5_xboole_0(A_19,k2_xboole_0(A_19,B_20))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_205])).

tff(c_1216,plain,(
    ! [A_19,B_20] : r1_xboole_0(k5_xboole_0(A_19,k2_xboole_0(A_19,B_20)),A_19) ),
    inference(resolution,[status(thm)],[c_1198,c_208])).

tff(c_1965,plain,(
    ! [A_208] : r1_xboole_0(k5_xboole_0(A_208,A_208),A_208) ),
    inference(superposition,[status(thm),theory(equality)],[c_1947,c_1216])).

tff(c_1229,plain,(
    ! [A_185] : k3_xboole_0(A_185,A_185) = A_185 ),
    inference(resolution,[status(thm)],[c_1198,c_10])).

tff(c_28,plain,(
    ! [A_28,B_29] : k2_xboole_0(k5_xboole_0(A_28,B_29),k3_xboole_0(A_28,B_29)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3190,plain,(
    ! [A_249] : k2_xboole_0(k5_xboole_0(A_249,A_249),A_249) = k2_xboole_0(A_249,A_249) ),
    inference(superposition,[status(thm),theory(equality)],[c_1229,c_28])).

tff(c_3224,plain,(
    ! [A_249] :
      ( k4_xboole_0(k2_xboole_0(A_249,A_249),A_249) = k5_xboole_0(A_249,A_249)
      | ~ r1_xboole_0(k5_xboole_0(A_249,A_249),A_249) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3190,c_24])).

tff(c_3251,plain,(
    ! [A_249] : k4_xboole_0(k2_xboole_0(A_249,A_249),A_249) = k5_xboole_0(A_249,A_249) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1965,c_3224])).

tff(c_8599,plain,(
    ! [A_249] : k5_xboole_0(A_249,A_249) = k4_xboole_0(A_249,A_249) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8549,c_3251])).

tff(c_8603,plain,(
    ! [A_249] : k5_xboole_0(A_249,A_249) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2444,c_8599])).

tff(c_3366,plain,(
    ! [A_254] : k4_xboole_0(k2_xboole_0(A_254,A_254),A_254) = k5_xboole_0(A_254,A_254) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1965,c_3224])).

tff(c_3420,plain,(
    ! [A_254] :
      ( k5_xboole_0(A_254,A_254) = A_254
      | ~ r1_xboole_0(A_254,A_254) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3366,c_24])).

tff(c_9359,plain,(
    ! [A_404] :
      ( k1_xboole_0 = A_404
      | ~ r1_xboole_0(A_404,A_404) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8603,c_3420])).

tff(c_10043,plain,(
    ! [B_425,D_426] :
      ( k2_zfmisc_1(B_425,D_426) = k1_xboole_0
      | ~ r1_xboole_0(B_425,B_425) ) ),
    inference(resolution,[status(thm)],[c_36,c_9359])).

tff(c_10080,plain,(
    ! [D_427] : k2_zfmisc_1(k1_xboole_0,D_427) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_180,c_10043])).

tff(c_60,plain,(
    ! [A_54,B_55] : v1_relat_1('#skF_2'(A_54,B_55)) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_56,plain,(
    ! [A_54,B_55] : k1_relat_1('#skF_2'(A_54,B_55)) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_343,plain,(
    ! [A_122] :
      ( k3_xboole_0(A_122,k2_zfmisc_1(k1_relat_1(A_122),k2_relat_1(A_122))) = A_122
      | ~ v1_relat_1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_367,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0('#skF_2'(A_54,B_55),k2_zfmisc_1(A_54,k2_relat_1('#skF_2'(A_54,B_55)))) = '#skF_2'(A_54,B_55)
      | ~ v1_relat_1('#skF_2'(A_54,B_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_343])).

tff(c_371,plain,(
    ! [A_54,B_55] : k3_xboole_0('#skF_2'(A_54,B_55),k2_zfmisc_1(A_54,k2_relat_1('#skF_2'(A_54,B_55)))) = '#skF_2'(A_54,B_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_367])).

tff(c_10086,plain,(
    ! [B_55] : k3_xboole_0('#skF_2'(k1_xboole_0,B_55),k1_xboole_0) = '#skF_2'(k1_xboole_0,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_10080,c_371])).

tff(c_10102,plain,(
    ! [B_55] : '#skF_2'(k1_xboole_0,B_55) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10086])).

tff(c_58,plain,(
    ! [A_54,B_55] : v1_funct_1('#skF_2'(A_54,B_55)) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1221,plain,(
    ! [A_183,B_184] :
      ( r2_hidden('#skF_1'(A_183,B_184),k1_relat_1(B_184))
      | v5_funct_1(B_184,A_183)
      | ~ v1_funct_1(B_184)
      | ~ v1_relat_1(B_184)
      | ~ v1_funct_1(A_183)
      | ~ v1_relat_1(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1224,plain,(
    ! [A_183,A_54,B_55] :
      ( r2_hidden('#skF_1'(A_183,'#skF_2'(A_54,B_55)),A_54)
      | v5_funct_1('#skF_2'(A_54,B_55),A_183)
      | ~ v1_funct_1('#skF_2'(A_54,B_55))
      | ~ v1_relat_1('#skF_2'(A_54,B_55))
      | ~ v1_funct_1(A_183)
      | ~ v1_relat_1(A_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1221])).

tff(c_6337,plain,(
    ! [A_349,A_350,B_351] :
      ( r2_hidden('#skF_1'(A_349,'#skF_2'(A_350,B_351)),A_350)
      | v5_funct_1('#skF_2'(A_350,B_351),A_349)
      | ~ v1_funct_1(A_349)
      | ~ v1_relat_1(A_349) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1224])).

tff(c_40,plain,(
    ! [C_40,B_39] : ~ r2_hidden(C_40,k4_xboole_0(B_39,k1_tarski(C_40))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_193,plain,(
    ! [C_96,A_97] :
      ( ~ r2_hidden(C_96,A_97)
      | ~ r1_xboole_0(A_97,k1_tarski(C_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_40])).

tff(c_198,plain,(
    ! [C_96] : ~ r2_hidden(C_96,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_180,c_193])).

tff(c_6372,plain,(
    ! [B_351,A_349] :
      ( v5_funct_1('#skF_2'(k1_xboole_0,B_351),A_349)
      | ~ v1_funct_1(A_349)
      | ~ v1_relat_1(A_349) ) ),
    inference(resolution,[status(thm)],[c_6337,c_198])).

tff(c_10827,plain,(
    ! [A_445] :
      ( v5_funct_1(k1_xboole_0,A_445)
      | ~ v1_funct_1(A_445)
      | ~ v1_relat_1(A_445) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10102,c_6372])).

tff(c_62,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_10830,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10827,c_62])).

tff(c_10834,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_10830])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:37:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.75/2.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.88/2.60  
% 6.88/2.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.88/2.60  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 6.88/2.60  
% 6.88/2.60  %Foreground sorts:
% 6.88/2.60  
% 6.88/2.60  
% 6.88/2.60  %Background operators:
% 6.88/2.60  
% 6.88/2.60  
% 6.88/2.60  %Foreground operators:
% 6.88/2.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.88/2.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.88/2.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.88/2.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.88/2.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.88/2.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.88/2.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.88/2.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.88/2.60  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 6.88/2.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.88/2.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.88/2.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.88/2.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.88/2.60  tff('#skF_3', type, '#skF_3': $i).
% 6.88/2.60  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.88/2.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.88/2.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.88/2.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.88/2.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.88/2.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.88/2.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.88/2.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.88/2.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.88/2.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.88/2.60  
% 6.88/2.62  tff(f_129, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 6.88/2.62  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 6.88/2.62  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.88/2.62  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.88/2.62  tff(f_67, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_xboole_1)).
% 6.88/2.62  tff(f_51, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 6.88/2.62  tff(f_65, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 6.88/2.62  tff(f_79, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 6.88/2.62  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_xboole_1)).
% 6.88/2.62  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_xboole_1)).
% 6.88/2.62  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 6.88/2.62  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 6.88/2.62  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k5_xboole_0(B, C)) <=> (r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, k3_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 6.88/2.62  tff(f_122, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 6.88/2.62  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 6.88/2.62  tff(f_110, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 6.88/2.62  tff(f_86, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 6.88/2.62  tff(c_66, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.88/2.62  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.88/2.62  tff(c_12, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.88/2.62  tff(c_20, plain, (![A_19, B_20]: (r1_tarski(A_19, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.88/2.62  tff(c_110, plain, (![A_77, B_78]: (k3_xboole_0(A_77, B_78)=A_77 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.88/2.62  tff(c_116, plain, (![A_80, B_81]: (k3_xboole_0(A_80, k2_xboole_0(A_80, B_81))=A_80)), inference(resolution, [status(thm)], [c_20, c_110])).
% 6.88/2.62  tff(c_26, plain, (![A_26, B_27]: (r1_xboole_0(k3_xboole_0(A_26, B_27), k4_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.88/2.62  tff(c_122, plain, (![A_80, B_81]: (r1_xboole_0(A_80, k4_xboole_0(A_80, k2_xboole_0(A_80, B_81))))), inference(superposition, [status(thm), theory('equality')], [c_116, c_26])).
% 6.88/2.62  tff(c_132, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | r1_xboole_0(A_84, k3_xboole_0(B_85, C_86)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.88/2.62  tff(c_139, plain, (![A_87, A_88]: (~r1_xboole_0(A_87, A_88) | r1_xboole_0(A_87, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_132])).
% 6.88/2.62  tff(c_149, plain, (![A_80]: (r1_xboole_0(A_80, k1_xboole_0))), inference(resolution, [status(thm)], [c_122, c_139])).
% 6.88/2.62  tff(c_160, plain, (![A_90, B_91]: (k4_xboole_0(k2_xboole_0(A_90, B_91), B_91)=A_90 | ~r1_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.88/2.62  tff(c_106, plain, (![A_75, B_76]: (r1_xboole_0(k3_xboole_0(A_75, B_76), k4_xboole_0(A_75, B_76)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.88/2.62  tff(c_109, plain, (![A_9]: (r1_xboole_0(k1_xboole_0, k4_xboole_0(A_9, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_106])).
% 6.88/2.62  tff(c_167, plain, (![A_90]: (r1_xboole_0(k1_xboole_0, A_90) | ~r1_xboole_0(A_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_160, c_109])).
% 6.88/2.62  tff(c_180, plain, (![A_90]: (r1_xboole_0(k1_xboole_0, A_90))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_167])).
% 6.88/2.62  tff(c_36, plain, (![A_34, B_35, C_36, D_37]: (~r1_xboole_0(A_34, B_35) | r1_xboole_0(k2_zfmisc_1(A_34, C_36), k2_zfmisc_1(B_35, D_37)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.88/2.62  tff(c_215, plain, (![A_112, B_113]: (k2_xboole_0(k5_xboole_0(A_112, B_113), k3_xboole_0(A_112, B_113))=k2_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.88/2.62  tff(c_263, plain, (![A_119]: (k2_xboole_0(k5_xboole_0(A_119, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_119, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_215])).
% 6.88/2.62  tff(c_24, plain, (![A_24, B_25]: (k4_xboole_0(k2_xboole_0(A_24, B_25), B_25)=A_24 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.88/2.62  tff(c_272, plain, (![A_119]: (k4_xboole_0(k2_xboole_0(A_119, k1_xboole_0), k1_xboole_0)=k5_xboole_0(A_119, k1_xboole_0) | ~r1_xboole_0(k5_xboole_0(A_119, k1_xboole_0), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_263, c_24])).
% 6.88/2.62  tff(c_290, plain, (![A_120]: (k4_xboole_0(k2_xboole_0(A_120, k1_xboole_0), k1_xboole_0)=k5_xboole_0(A_120, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_272])).
% 6.88/2.62  tff(c_299, plain, (![A_120]: (k5_xboole_0(A_120, k1_xboole_0)=A_120 | ~r1_xboole_0(A_120, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_290, c_24])).
% 6.88/2.62  tff(c_315, plain, (![A_120]: (k5_xboole_0(A_120, k1_xboole_0)=A_120)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_299])).
% 6.88/2.62  tff(c_287, plain, (![A_119]: (k4_xboole_0(k2_xboole_0(A_119, k1_xboole_0), k1_xboole_0)=k5_xboole_0(A_119, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_272])).
% 6.88/2.62  tff(c_321, plain, (![A_119]: (k4_xboole_0(k2_xboole_0(A_119, k1_xboole_0), k1_xboole_0)=A_119)), inference(demodulation, [status(thm), theory('equality')], [c_315, c_287])).
% 6.88/2.62  tff(c_708, plain, (![A_165, B_166, C_167]: (k4_xboole_0(k3_xboole_0(A_165, B_166), k3_xboole_0(C_167, B_166))=k3_xboole_0(k4_xboole_0(A_165, C_167), B_166))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.88/2.62  tff(c_756, plain, (![C_167, A_9]: (k4_xboole_0(k1_xboole_0, k3_xboole_0(C_167, k1_xboole_0))=k3_xboole_0(k4_xboole_0(A_9, C_167), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_708])).
% 6.88/2.62  tff(c_762, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_756])).
% 6.88/2.62  tff(c_800, plain, (![A_169, B_170, C_171]: (k2_xboole_0(k4_xboole_0(A_169, B_170), k3_xboole_0(A_169, C_171))=k4_xboole_0(A_169, k4_xboole_0(B_170, C_171)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.88/2.62  tff(c_1070, plain, (![A_175, B_176, C_177]: (r1_tarski(k4_xboole_0(A_175, B_176), k4_xboole_0(A_175, k4_xboole_0(B_176, C_177))))), inference(superposition, [status(thm), theory('equality')], [c_800, c_20])).
% 6.88/2.62  tff(c_1156, plain, (![A_181]: (r1_tarski(k4_xboole_0(A_181, k1_xboole_0), k4_xboole_0(A_181, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_762, c_1070])).
% 6.88/2.62  tff(c_1181, plain, (![A_24]: (r1_tarski(A_24, k4_xboole_0(k2_xboole_0(A_24, k1_xboole_0), k1_xboole_0)) | ~r1_xboole_0(A_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1156])).
% 6.88/2.62  tff(c_1194, plain, (![A_24]: (r1_tarski(A_24, A_24))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_321, c_1181])).
% 6.88/2.62  tff(c_1544, plain, (![A_201, B_202]: (k4_xboole_0(A_201, k4_xboole_0(B_202, k1_xboole_0))=k2_xboole_0(k4_xboole_0(A_201, B_202), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_800])).
% 6.88/2.62  tff(c_1653, plain, (![A_205]: (k2_xboole_0(k4_xboole_0(A_205, k1_xboole_0), k1_xboole_0)=k4_xboole_0(A_205, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_762, c_1544])).
% 6.88/2.62  tff(c_1735, plain, (![A_24]: (k4_xboole_0(k2_xboole_0(A_24, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_24, k1_xboole_0) | ~r1_xboole_0(A_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1653])).
% 6.88/2.62  tff(c_1755, plain, (![A_24]: (k2_xboole_0(A_24, k1_xboole_0)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_321, c_1735])).
% 6.88/2.62  tff(c_14, plain, (![A_10, B_11, C_12]: (r1_tarski(k4_xboole_0(A_10, B_11), C_12) | ~r1_tarski(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.88/2.62  tff(c_1728, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k2_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_762, c_1653])).
% 6.88/2.62  tff(c_1752, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_762, c_1728])).
% 6.88/2.62  tff(c_323, plain, (![A_121]: (k5_xboole_0(A_121, k1_xboole_0)=A_121)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_299])).
% 6.88/2.62  tff(c_6, plain, (![A_1, B_2, C_3]: (r1_tarski(A_1, k2_xboole_0(B_2, C_3)) | ~r1_tarski(A_1, k5_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.88/2.62  tff(c_403, plain, (![A_124, A_125]: (r1_tarski(A_124, k2_xboole_0(A_125, k1_xboole_0)) | ~r1_tarski(A_124, A_125))), inference(superposition, [status(thm), theory('equality')], [c_323, c_6])).
% 6.88/2.62  tff(c_10, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.88/2.62  tff(c_407, plain, (![A_124, A_125]: (k3_xboole_0(A_124, k2_xboole_0(A_125, k1_xboole_0))=A_124 | ~r1_tarski(A_124, A_125))), inference(resolution, [status(thm)], [c_403, c_10])).
% 6.88/2.62  tff(c_1874, plain, (![A_124]: (k3_xboole_0(A_124, k1_xboole_0)=A_124 | ~r1_tarski(A_124, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1752, c_407])).
% 6.88/2.62  tff(c_2104, plain, (![A_212]: (k1_xboole_0=A_212 | ~r1_tarski(A_212, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1874])).
% 6.88/2.62  tff(c_2124, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_tarski(A_10, k2_xboole_0(B_11, k1_xboole_0)))), inference(resolution, [status(thm)], [c_14, c_2104])).
% 6.88/2.62  tff(c_2407, plain, (![A_224, B_225]: (k4_xboole_0(A_224, B_225)=k1_xboole_0 | ~r1_tarski(A_224, B_225))), inference(demodulation, [status(thm), theory('equality')], [c_1755, c_2124])).
% 6.88/2.62  tff(c_2444, plain, (![A_24]: (k4_xboole_0(A_24, A_24)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1194, c_2407])).
% 6.88/2.62  tff(c_1198, plain, (![A_182]: (r1_tarski(A_182, A_182))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_321, c_1181])).
% 6.88/2.62  tff(c_1219, plain, (![A_182]: (k3_xboole_0(A_182, A_182)=A_182)), inference(resolution, [status(thm)], [c_1198, c_10])).
% 6.88/2.62  tff(c_1942, plain, (![A_119]: (k4_xboole_0(A_119, k1_xboole_0)=A_119)), inference(demodulation, [status(thm), theory('equality')], [c_1755, c_321])).
% 6.88/2.62  tff(c_770, plain, (![C_12]: (r1_tarski(k1_xboole_0, C_12) | ~r1_tarski(k1_xboole_0, k2_xboole_0(k1_xboole_0, C_12)))), inference(superposition, [status(thm), theory('equality')], [c_762, c_14])).
% 6.88/2.62  tff(c_779, plain, (![C_12]: (r1_tarski(k1_xboole_0, C_12))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_770])).
% 6.88/2.62  tff(c_2446, plain, (![C_12]: (k4_xboole_0(k1_xboole_0, C_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_779, c_2407])).
% 6.88/2.62  tff(c_8055, plain, (![A_390, B_391, C_392]: (k4_xboole_0(k2_xboole_0(A_390, B_391), k4_xboole_0(B_391, C_392))=k2_xboole_0(A_390, k3_xboole_0(k2_xboole_0(A_390, B_391), C_392)) | ~r1_xboole_0(A_390, B_391))), inference(superposition, [status(thm), theory('equality')], [c_24, c_800])).
% 6.88/2.62  tff(c_8318, plain, (![A_24, C_392]: (k2_xboole_0(A_24, k3_xboole_0(k2_xboole_0(A_24, k1_xboole_0), C_392))=k4_xboole_0(A_24, k4_xboole_0(k1_xboole_0, C_392)) | ~r1_xboole_0(A_24, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1755, c_8055])).
% 6.88/2.62  tff(c_8401, plain, (![A_393, C_394]: (k2_xboole_0(A_393, k3_xboole_0(A_393, C_394))=A_393)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_1942, c_2446, c_1755, c_8318])).
% 6.88/2.62  tff(c_8549, plain, (![A_182]: (k2_xboole_0(A_182, A_182)=A_182)), inference(superposition, [status(thm), theory('equality')], [c_1219, c_8401])).
% 6.88/2.62  tff(c_1947, plain, (![A_208]: (k2_xboole_0(A_208, k1_xboole_0)=A_208)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_321, c_1735])).
% 6.88/2.62  tff(c_114, plain, (![A_19, B_20]: (k3_xboole_0(A_19, k2_xboole_0(A_19, B_20))=A_19)), inference(resolution, [status(thm)], [c_20, c_110])).
% 6.88/2.62  tff(c_205, plain, (![A_102, B_103, C_104]: (r1_xboole_0(A_102, k3_xboole_0(B_103, C_104)) | ~r1_tarski(A_102, k5_xboole_0(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.88/2.62  tff(c_208, plain, (![A_102, A_19, B_20]: (r1_xboole_0(A_102, A_19) | ~r1_tarski(A_102, k5_xboole_0(A_19, k2_xboole_0(A_19, B_20))))), inference(superposition, [status(thm), theory('equality')], [c_114, c_205])).
% 6.88/2.62  tff(c_1216, plain, (![A_19, B_20]: (r1_xboole_0(k5_xboole_0(A_19, k2_xboole_0(A_19, B_20)), A_19))), inference(resolution, [status(thm)], [c_1198, c_208])).
% 6.88/2.62  tff(c_1965, plain, (![A_208]: (r1_xboole_0(k5_xboole_0(A_208, A_208), A_208))), inference(superposition, [status(thm), theory('equality')], [c_1947, c_1216])).
% 6.88/2.62  tff(c_1229, plain, (![A_185]: (k3_xboole_0(A_185, A_185)=A_185)), inference(resolution, [status(thm)], [c_1198, c_10])).
% 6.88/2.62  tff(c_28, plain, (![A_28, B_29]: (k2_xboole_0(k5_xboole_0(A_28, B_29), k3_xboole_0(A_28, B_29))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.88/2.62  tff(c_3190, plain, (![A_249]: (k2_xboole_0(k5_xboole_0(A_249, A_249), A_249)=k2_xboole_0(A_249, A_249))), inference(superposition, [status(thm), theory('equality')], [c_1229, c_28])).
% 6.88/2.62  tff(c_3224, plain, (![A_249]: (k4_xboole_0(k2_xboole_0(A_249, A_249), A_249)=k5_xboole_0(A_249, A_249) | ~r1_xboole_0(k5_xboole_0(A_249, A_249), A_249))), inference(superposition, [status(thm), theory('equality')], [c_3190, c_24])).
% 6.88/2.62  tff(c_3251, plain, (![A_249]: (k4_xboole_0(k2_xboole_0(A_249, A_249), A_249)=k5_xboole_0(A_249, A_249))), inference(demodulation, [status(thm), theory('equality')], [c_1965, c_3224])).
% 6.88/2.62  tff(c_8599, plain, (![A_249]: (k5_xboole_0(A_249, A_249)=k4_xboole_0(A_249, A_249))), inference(demodulation, [status(thm), theory('equality')], [c_8549, c_3251])).
% 6.88/2.62  tff(c_8603, plain, (![A_249]: (k5_xboole_0(A_249, A_249)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2444, c_8599])).
% 6.88/2.62  tff(c_3366, plain, (![A_254]: (k4_xboole_0(k2_xboole_0(A_254, A_254), A_254)=k5_xboole_0(A_254, A_254))), inference(demodulation, [status(thm), theory('equality')], [c_1965, c_3224])).
% 6.88/2.62  tff(c_3420, plain, (![A_254]: (k5_xboole_0(A_254, A_254)=A_254 | ~r1_xboole_0(A_254, A_254))), inference(superposition, [status(thm), theory('equality')], [c_3366, c_24])).
% 6.88/2.62  tff(c_9359, plain, (![A_404]: (k1_xboole_0=A_404 | ~r1_xboole_0(A_404, A_404))), inference(demodulation, [status(thm), theory('equality')], [c_8603, c_3420])).
% 6.88/2.62  tff(c_10043, plain, (![B_425, D_426]: (k2_zfmisc_1(B_425, D_426)=k1_xboole_0 | ~r1_xboole_0(B_425, B_425))), inference(resolution, [status(thm)], [c_36, c_9359])).
% 6.88/2.62  tff(c_10080, plain, (![D_427]: (k2_zfmisc_1(k1_xboole_0, D_427)=k1_xboole_0)), inference(resolution, [status(thm)], [c_180, c_10043])).
% 6.88/2.62  tff(c_60, plain, (![A_54, B_55]: (v1_relat_1('#skF_2'(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.88/2.62  tff(c_56, plain, (![A_54, B_55]: (k1_relat_1('#skF_2'(A_54, B_55))=A_54)), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.88/2.62  tff(c_343, plain, (![A_122]: (k3_xboole_0(A_122, k2_zfmisc_1(k1_relat_1(A_122), k2_relat_1(A_122)))=A_122 | ~v1_relat_1(A_122))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.88/2.62  tff(c_367, plain, (![A_54, B_55]: (k3_xboole_0('#skF_2'(A_54, B_55), k2_zfmisc_1(A_54, k2_relat_1('#skF_2'(A_54, B_55))))='#skF_2'(A_54, B_55) | ~v1_relat_1('#skF_2'(A_54, B_55)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_343])).
% 6.88/2.62  tff(c_371, plain, (![A_54, B_55]: (k3_xboole_0('#skF_2'(A_54, B_55), k2_zfmisc_1(A_54, k2_relat_1('#skF_2'(A_54, B_55))))='#skF_2'(A_54, B_55))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_367])).
% 6.88/2.62  tff(c_10086, plain, (![B_55]: (k3_xboole_0('#skF_2'(k1_xboole_0, B_55), k1_xboole_0)='#skF_2'(k1_xboole_0, B_55))), inference(superposition, [status(thm), theory('equality')], [c_10080, c_371])).
% 6.88/2.62  tff(c_10102, plain, (![B_55]: ('#skF_2'(k1_xboole_0, B_55)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10086])).
% 6.88/2.62  tff(c_58, plain, (![A_54, B_55]: (v1_funct_1('#skF_2'(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.88/2.62  tff(c_1221, plain, (![A_183, B_184]: (r2_hidden('#skF_1'(A_183, B_184), k1_relat_1(B_184)) | v5_funct_1(B_184, A_183) | ~v1_funct_1(B_184) | ~v1_relat_1(B_184) | ~v1_funct_1(A_183) | ~v1_relat_1(A_183))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.88/2.62  tff(c_1224, plain, (![A_183, A_54, B_55]: (r2_hidden('#skF_1'(A_183, '#skF_2'(A_54, B_55)), A_54) | v5_funct_1('#skF_2'(A_54, B_55), A_183) | ~v1_funct_1('#skF_2'(A_54, B_55)) | ~v1_relat_1('#skF_2'(A_54, B_55)) | ~v1_funct_1(A_183) | ~v1_relat_1(A_183))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1221])).
% 6.88/2.62  tff(c_6337, plain, (![A_349, A_350, B_351]: (r2_hidden('#skF_1'(A_349, '#skF_2'(A_350, B_351)), A_350) | v5_funct_1('#skF_2'(A_350, B_351), A_349) | ~v1_funct_1(A_349) | ~v1_relat_1(A_349))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1224])).
% 6.88/2.62  tff(c_40, plain, (![C_40, B_39]: (~r2_hidden(C_40, k4_xboole_0(B_39, k1_tarski(C_40))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.88/2.62  tff(c_193, plain, (![C_96, A_97]: (~r2_hidden(C_96, A_97) | ~r1_xboole_0(A_97, k1_tarski(C_96)))), inference(superposition, [status(thm), theory('equality')], [c_160, c_40])).
% 6.88/2.62  tff(c_198, plain, (![C_96]: (~r2_hidden(C_96, k1_xboole_0))), inference(resolution, [status(thm)], [c_180, c_193])).
% 6.88/2.62  tff(c_6372, plain, (![B_351, A_349]: (v5_funct_1('#skF_2'(k1_xboole_0, B_351), A_349) | ~v1_funct_1(A_349) | ~v1_relat_1(A_349))), inference(resolution, [status(thm)], [c_6337, c_198])).
% 6.88/2.62  tff(c_10827, plain, (![A_445]: (v5_funct_1(k1_xboole_0, A_445) | ~v1_funct_1(A_445) | ~v1_relat_1(A_445))), inference(demodulation, [status(thm), theory('equality')], [c_10102, c_6372])).
% 6.88/2.62  tff(c_62, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.88/2.62  tff(c_10830, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10827, c_62])).
% 6.88/2.62  tff(c_10834, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_10830])).
% 6.88/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.88/2.62  
% 6.88/2.62  Inference rules
% 6.88/2.62  ----------------------
% 6.88/2.62  #Ref     : 0
% 6.88/2.62  #Sup     : 2533
% 6.88/2.62  #Fact    : 0
% 6.88/2.62  #Define  : 0
% 6.88/2.62  #Split   : 2
% 6.88/2.62  #Chain   : 0
% 6.88/2.62  #Close   : 0
% 6.88/2.62  
% 6.88/2.62  Ordering : KBO
% 6.88/2.62  
% 6.88/2.62  Simplification rules
% 6.88/2.62  ----------------------
% 6.88/2.62  #Subsume      : 110
% 6.88/2.62  #Demod        : 2441
% 6.88/2.62  #Tautology    : 1366
% 6.88/2.62  #SimpNegUnit  : 17
% 6.88/2.62  #BackRed      : 58
% 6.88/2.62  
% 6.88/2.62  #Partial instantiations: 0
% 6.88/2.62  #Strategies tried      : 1
% 6.88/2.62  
% 6.88/2.62  Timing (in seconds)
% 6.88/2.62  ----------------------
% 6.88/2.62  Preprocessing        : 0.35
% 6.88/2.62  Parsing              : 0.19
% 6.88/2.62  CNF conversion       : 0.02
% 6.88/2.62  Main loop            : 1.43
% 6.88/2.62  Inferencing          : 0.44
% 6.88/2.63  Reduction            : 0.57
% 6.88/2.63  Demodulation         : 0.44
% 6.88/2.63  BG Simplification    : 0.06
% 6.88/2.63  Subsumption          : 0.25
% 6.88/2.63  Abstraction          : 0.07
% 6.88/2.63  MUC search           : 0.00
% 6.88/2.63  Cooper               : 0.00
% 6.88/2.63  Total                : 1.82
% 6.88/2.63  Index Insertion      : 0.00
% 6.88/2.63  Index Deletion       : 0.00
% 6.88/2.63  Index Matching       : 0.00
% 6.88/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
