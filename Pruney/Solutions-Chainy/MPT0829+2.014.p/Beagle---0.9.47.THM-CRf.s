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
% DateTime   : Thu Dec  3 10:07:23 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 299 expanded)
%              Number of leaves         :   41 ( 119 expanded)
%              Depth                    :   13
%              Number of atoms          :  128 ( 551 expanded)
%              Number of equality atoms :   37 ( 158 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_90,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1581,plain,(
    ! [A_196,B_197,C_198] :
      ( k2_relset_1(A_196,B_197,C_198) = k2_relat_1(C_198)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1585,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1581])).

tff(c_50,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_110,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_52,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_867,plain,(
    ! [C_126,A_127,B_128,D_129] :
      ( r1_tarski(C_126,k1_relset_1(A_127,B_128,D_129))
      | ~ r1_tarski(k6_relat_1(C_126),D_129)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_917,plain,(
    ! [A_132,B_133] :
      ( r1_tarski('#skF_2',k1_relset_1(A_132,B_133,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(resolution,[status(thm)],[c_52,c_867])).

tff(c_920,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_917])).

tff(c_924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_920])).

tff(c_925,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1586,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1585,c_925])).

tff(c_1758,plain,(
    ! [C_205,A_206,B_207,D_208] :
      ( r1_tarski(C_205,k2_relset_1(A_206,B_207,D_208))
      | ~ r1_tarski(k6_relat_1(C_205),D_208)
      | ~ m1_subset_1(D_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1798,plain,(
    ! [A_211,B_212] :
      ( r1_tarski('#skF_2',k2_relset_1(A_211,B_212,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(resolution,[status(thm)],[c_52,c_1758])).

tff(c_1801,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_1798])).

tff(c_1803,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1585,c_1801])).

tff(c_26,plain,(
    ! [A_28] : k1_relat_1(k6_relat_1(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [A_31] : v1_relat_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1048,plain,(
    ! [A_155,B_156] :
      ( k5_relat_1(k6_relat_1(A_155),B_156) = k7_relat_1(B_156,A_155)
      | ~ v1_relat_1(B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    ! [B_33,A_32] : k5_relat_1(k6_relat_1(B_33),k6_relat_1(A_32)) = k6_relat_1(k3_xboole_0(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1055,plain,(
    ! [A_32,A_155] :
      ( k7_relat_1(k6_relat_1(A_32),A_155) = k6_relat_1(k3_xboole_0(A_32,A_155))
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1048,c_38])).

tff(c_1064,plain,(
    ! [A_32,A_155] : k7_relat_1(k6_relat_1(A_32),A_155) = k6_relat_1(k3_xboole_0(A_32,A_155)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1055])).

tff(c_34,plain,(
    ! [A_31] : v4_relat_1(k6_relat_1(A_31),A_31) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1222,plain,(
    ! [C_176,B_177,A_178] :
      ( v4_relat_1(C_176,B_177)
      | ~ v4_relat_1(C_176,A_178)
      | ~ v1_relat_1(C_176)
      | ~ r1_tarski(A_178,B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1226,plain,(
    ! [A_31,B_177] :
      ( v4_relat_1(k6_relat_1(A_31),B_177)
      | ~ v1_relat_1(k6_relat_1(A_31))
      | ~ r1_tarski(A_31,B_177) ) ),
    inference(resolution,[status(thm)],[c_34,c_1222])).

tff(c_1261,plain,(
    ! [A_181,B_182] :
      ( v4_relat_1(k6_relat_1(A_181),B_182)
      | ~ r1_tarski(A_181,B_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1226])).

tff(c_22,plain,(
    ! [B_23,A_22] :
      ( k7_relat_1(B_23,A_22) = B_23
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1266,plain,(
    ! [A_181,B_182] :
      ( k7_relat_1(k6_relat_1(A_181),B_182) = k6_relat_1(A_181)
      | ~ v1_relat_1(k6_relat_1(A_181))
      | ~ r1_tarski(A_181,B_182) ) ),
    inference(resolution,[status(thm)],[c_1261,c_22])).

tff(c_1281,plain,(
    ! [A_184,B_185] :
      ( k6_relat_1(k3_xboole_0(A_184,B_185)) = k6_relat_1(A_184)
      | ~ r1_tarski(A_184,B_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1064,c_1266])).

tff(c_1311,plain,(
    ! [A_184,B_185] :
      ( k3_xboole_0(A_184,B_185) = k1_relat_1(k6_relat_1(A_184))
      | ~ r1_tarski(A_184,B_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1281,c_26])).

tff(c_1340,plain,(
    ! [A_184,B_185] :
      ( k3_xboole_0(A_184,B_185) = A_184
      | ~ r1_tarski(A_184,B_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1311])).

tff(c_1814,plain,(
    k3_xboole_0('#skF_2',k2_relat_1('#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1803,c_1340])).

tff(c_16,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_974,plain,(
    ! [B_140,A_141] :
      ( v1_relat_1(B_140)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(A_141))
      | ~ v1_relat_1(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_977,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_974])).

tff(c_980,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_977])).

tff(c_1022,plain,(
    ! [C_148,B_149,A_150] :
      ( v5_relat_1(C_148,B_149)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_150,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1026,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1022])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_936,plain,(
    ! [A_136,B_137] : k1_setfam_1(k2_tarski(A_136,B_137)) = k3_xboole_0(A_136,B_137) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_951,plain,(
    ! [B_138,A_139] : k1_setfam_1(k2_tarski(B_138,A_139)) = k3_xboole_0(A_139,B_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_936])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_957,plain,(
    ! [B_138,A_139] : k3_xboole_0(B_138,A_139) = k3_xboole_0(A_139,B_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_951,c_8])).

tff(c_1331,plain,(
    ! [B_138,A_139] :
      ( k6_relat_1(k3_xboole_0(B_138,A_139)) = k6_relat_1(A_139)
      | ~ r1_tarski(A_139,B_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_957,c_1281])).

tff(c_1827,plain,
    ( k6_relat_1(k2_relat_1('#skF_3')) = k6_relat_1('#skF_2')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1814,c_1331])).

tff(c_2050,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1827])).

tff(c_2053,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_2050])).

tff(c_2057,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_980,c_1026,c_2053])).

tff(c_2059,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1827])).

tff(c_1475,plain,(
    ! [B_192,A_193] :
      ( k6_relat_1(k3_xboole_0(B_192,A_193)) = k6_relat_1(A_193)
      | ~ r1_tarski(A_193,B_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_957,c_1281])).

tff(c_1511,plain,(
    ! [B_192,A_193] :
      ( k3_xboole_0(B_192,A_193) = k1_relat_1(k6_relat_1(A_193))
      | ~ r1_tarski(A_193,B_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1475,c_26])).

tff(c_1552,plain,(
    ! [B_192,A_193] :
      ( k3_xboole_0(B_192,A_193) = A_193
      | ~ r1_tarski(A_193,B_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1511])).

tff(c_2064,plain,(
    k3_xboole_0('#skF_2',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2059,c_1552])).

tff(c_2073,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1814,c_2064])).

tff(c_2075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1586,c_2073])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.94/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.85  
% 3.94/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.85  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.94/1.85  
% 3.94/1.85  %Foreground sorts:
% 3.94/1.85  
% 3.94/1.85  
% 3.94/1.85  %Background operators:
% 3.94/1.85  
% 3.94/1.85  
% 3.94/1.85  %Foreground operators:
% 3.94/1.85  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.94/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.94/1.85  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.94/1.85  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.94/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.94/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.94/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.94/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.94/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.94/1.85  tff('#skF_2', type, '#skF_2': $i).
% 3.94/1.85  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.94/1.85  tff('#skF_3', type, '#skF_3': $i).
% 3.94/1.85  tff('#skF_1', type, '#skF_1': $i).
% 3.94/1.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.94/1.85  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.94/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.94/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.94/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.94/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.94/1.85  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.94/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.94/1.85  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.94/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.94/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.94/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.94/1.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.94/1.85  
% 3.94/1.86  tff(f_117, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relset_1)).
% 3.94/1.86  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.94/1.86  tff(f_108, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 3.94/1.86  tff(f_78, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.94/1.86  tff(f_88, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 3.94/1.86  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.94/1.86  tff(f_90, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.94/1.86  tff(f_74, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t217_relat_1)).
% 3.94/1.86  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.94/1.86  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.94/1.86  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.94/1.86  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.94/1.86  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.94/1.86  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.94/1.86  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.94/1.86  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.94/1.86  tff(c_1581, plain, (![A_196, B_197, C_198]: (k2_relset_1(A_196, B_197, C_198)=k2_relat_1(C_198) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.94/1.86  tff(c_1585, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1581])).
% 3.94/1.86  tff(c_50, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.94/1.86  tff(c_110, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_50])).
% 3.94/1.86  tff(c_52, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.94/1.86  tff(c_867, plain, (![C_126, A_127, B_128, D_129]: (r1_tarski(C_126, k1_relset_1(A_127, B_128, D_129)) | ~r1_tarski(k6_relat_1(C_126), D_129) | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.94/1.86  tff(c_917, plain, (![A_132, B_133]: (r1_tarski('#skF_2', k1_relset_1(A_132, B_133, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(resolution, [status(thm)], [c_52, c_867])).
% 3.94/1.86  tff(c_920, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_917])).
% 3.94/1.86  tff(c_924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_920])).
% 3.94/1.86  tff(c_925, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_50])).
% 3.94/1.86  tff(c_1586, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1585, c_925])).
% 3.94/1.86  tff(c_1758, plain, (![C_205, A_206, B_207, D_208]: (r1_tarski(C_205, k2_relset_1(A_206, B_207, D_208)) | ~r1_tarski(k6_relat_1(C_205), D_208) | ~m1_subset_1(D_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.94/1.86  tff(c_1798, plain, (![A_211, B_212]: (r1_tarski('#skF_2', k2_relset_1(A_211, B_212, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(resolution, [status(thm)], [c_52, c_1758])).
% 3.94/1.86  tff(c_1801, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_1798])).
% 3.94/1.86  tff(c_1803, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1585, c_1801])).
% 3.94/1.86  tff(c_26, plain, (![A_28]: (k1_relat_1(k6_relat_1(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.94/1.86  tff(c_32, plain, (![A_31]: (v1_relat_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.94/1.86  tff(c_1048, plain, (![A_155, B_156]: (k5_relat_1(k6_relat_1(A_155), B_156)=k7_relat_1(B_156, A_155) | ~v1_relat_1(B_156))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.94/1.86  tff(c_38, plain, (![B_33, A_32]: (k5_relat_1(k6_relat_1(B_33), k6_relat_1(A_32))=k6_relat_1(k3_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.94/1.86  tff(c_1055, plain, (![A_32, A_155]: (k7_relat_1(k6_relat_1(A_32), A_155)=k6_relat_1(k3_xboole_0(A_32, A_155)) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_1048, c_38])).
% 3.94/1.86  tff(c_1064, plain, (![A_32, A_155]: (k7_relat_1(k6_relat_1(A_32), A_155)=k6_relat_1(k3_xboole_0(A_32, A_155)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1055])).
% 3.94/1.86  tff(c_34, plain, (![A_31]: (v4_relat_1(k6_relat_1(A_31), A_31))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.94/1.86  tff(c_1222, plain, (![C_176, B_177, A_178]: (v4_relat_1(C_176, B_177) | ~v4_relat_1(C_176, A_178) | ~v1_relat_1(C_176) | ~r1_tarski(A_178, B_177))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.94/1.86  tff(c_1226, plain, (![A_31, B_177]: (v4_relat_1(k6_relat_1(A_31), B_177) | ~v1_relat_1(k6_relat_1(A_31)) | ~r1_tarski(A_31, B_177))), inference(resolution, [status(thm)], [c_34, c_1222])).
% 3.94/1.86  tff(c_1261, plain, (![A_181, B_182]: (v4_relat_1(k6_relat_1(A_181), B_182) | ~r1_tarski(A_181, B_182))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1226])).
% 3.94/1.86  tff(c_22, plain, (![B_23, A_22]: (k7_relat_1(B_23, A_22)=B_23 | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.94/1.86  tff(c_1266, plain, (![A_181, B_182]: (k7_relat_1(k6_relat_1(A_181), B_182)=k6_relat_1(A_181) | ~v1_relat_1(k6_relat_1(A_181)) | ~r1_tarski(A_181, B_182))), inference(resolution, [status(thm)], [c_1261, c_22])).
% 3.94/1.86  tff(c_1281, plain, (![A_184, B_185]: (k6_relat_1(k3_xboole_0(A_184, B_185))=k6_relat_1(A_184) | ~r1_tarski(A_184, B_185))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1064, c_1266])).
% 3.94/1.86  tff(c_1311, plain, (![A_184, B_185]: (k3_xboole_0(A_184, B_185)=k1_relat_1(k6_relat_1(A_184)) | ~r1_tarski(A_184, B_185))), inference(superposition, [status(thm), theory('equality')], [c_1281, c_26])).
% 3.94/1.86  tff(c_1340, plain, (![A_184, B_185]: (k3_xboole_0(A_184, B_185)=A_184 | ~r1_tarski(A_184, B_185))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1311])).
% 3.94/1.86  tff(c_1814, plain, (k3_xboole_0('#skF_2', k2_relat_1('#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_1803, c_1340])).
% 3.94/1.86  tff(c_16, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.94/1.86  tff(c_974, plain, (![B_140, A_141]: (v1_relat_1(B_140) | ~m1_subset_1(B_140, k1_zfmisc_1(A_141)) | ~v1_relat_1(A_141))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.94/1.86  tff(c_977, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_974])).
% 3.94/1.86  tff(c_980, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_977])).
% 3.94/1.86  tff(c_1022, plain, (![C_148, B_149, A_150]: (v5_relat_1(C_148, B_149) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_150, B_149))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.94/1.86  tff(c_1026, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_1022])).
% 3.94/1.86  tff(c_14, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.94/1.86  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.94/1.86  tff(c_936, plain, (![A_136, B_137]: (k1_setfam_1(k2_tarski(A_136, B_137))=k3_xboole_0(A_136, B_137))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.94/1.86  tff(c_951, plain, (![B_138, A_139]: (k1_setfam_1(k2_tarski(B_138, A_139))=k3_xboole_0(A_139, B_138))), inference(superposition, [status(thm), theory('equality')], [c_2, c_936])).
% 3.94/1.86  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.94/1.86  tff(c_957, plain, (![B_138, A_139]: (k3_xboole_0(B_138, A_139)=k3_xboole_0(A_139, B_138))), inference(superposition, [status(thm), theory('equality')], [c_951, c_8])).
% 3.94/1.86  tff(c_1331, plain, (![B_138, A_139]: (k6_relat_1(k3_xboole_0(B_138, A_139))=k6_relat_1(A_139) | ~r1_tarski(A_139, B_138))), inference(superposition, [status(thm), theory('equality')], [c_957, c_1281])).
% 3.94/1.86  tff(c_1827, plain, (k6_relat_1(k2_relat_1('#skF_3'))=k6_relat_1('#skF_2') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1814, c_1331])).
% 3.94/1.86  tff(c_2050, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1827])).
% 3.94/1.86  tff(c_2053, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_2050])).
% 3.94/1.86  tff(c_2057, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_980, c_1026, c_2053])).
% 3.94/1.86  tff(c_2059, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_1827])).
% 3.94/1.86  tff(c_1475, plain, (![B_192, A_193]: (k6_relat_1(k3_xboole_0(B_192, A_193))=k6_relat_1(A_193) | ~r1_tarski(A_193, B_192))), inference(superposition, [status(thm), theory('equality')], [c_957, c_1281])).
% 3.94/1.86  tff(c_1511, plain, (![B_192, A_193]: (k3_xboole_0(B_192, A_193)=k1_relat_1(k6_relat_1(A_193)) | ~r1_tarski(A_193, B_192))), inference(superposition, [status(thm), theory('equality')], [c_1475, c_26])).
% 3.94/1.86  tff(c_1552, plain, (![B_192, A_193]: (k3_xboole_0(B_192, A_193)=A_193 | ~r1_tarski(A_193, B_192))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1511])).
% 3.94/1.86  tff(c_2064, plain, (k3_xboole_0('#skF_2', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2059, c_1552])).
% 3.94/1.86  tff(c_2073, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1814, c_2064])).
% 3.94/1.86  tff(c_2075, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1586, c_2073])).
% 3.94/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.86  
% 3.94/1.86  Inference rules
% 3.94/1.86  ----------------------
% 3.94/1.86  #Ref     : 0
% 3.94/1.86  #Sup     : 493
% 3.94/1.86  #Fact    : 0
% 3.94/1.86  #Define  : 0
% 3.94/1.86  #Split   : 7
% 3.94/1.86  #Chain   : 0
% 3.94/1.86  #Close   : 0
% 3.94/1.86  
% 3.94/1.86  Ordering : KBO
% 3.94/1.86  
% 3.94/1.86  Simplification rules
% 3.94/1.86  ----------------------
% 3.94/1.86  #Subsume      : 45
% 3.94/1.86  #Demod        : 240
% 3.94/1.86  #Tautology    : 230
% 3.94/1.86  #SimpNegUnit  : 4
% 3.94/1.86  #BackRed      : 1
% 3.94/1.86  
% 3.94/1.86  #Partial instantiations: 0
% 3.94/1.86  #Strategies tried      : 1
% 3.94/1.86  
% 3.94/1.86  Timing (in seconds)
% 3.94/1.86  ----------------------
% 3.94/1.87  Preprocessing        : 0.51
% 3.94/1.87  Parsing              : 0.30
% 3.94/1.87  CNF conversion       : 0.02
% 3.94/1.87  Main loop            : 0.57
% 3.94/1.87  Inferencing          : 0.20
% 3.94/1.87  Reduction            : 0.21
% 3.94/1.87  Demodulation         : 0.16
% 3.94/1.87  BG Simplification    : 0.03
% 3.94/1.87  Subsumption          : 0.09
% 3.94/1.87  Abstraction          : 0.03
% 3.94/1.87  MUC search           : 0.00
% 3.94/1.87  Cooper               : 0.00
% 3.94/1.87  Total                : 1.11
% 3.94/1.87  Index Insertion      : 0.00
% 3.94/1.87  Index Deletion       : 0.00
% 3.94/1.87  Index Matching       : 0.00
% 3.94/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
