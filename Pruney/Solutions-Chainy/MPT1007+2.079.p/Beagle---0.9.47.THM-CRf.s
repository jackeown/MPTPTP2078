%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:21 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 145 expanded)
%              Number of leaves         :   43 (  70 expanded)
%              Depth                    :   15
%              Number of atoms          :  136 ( 279 expanded)
%              Number of equality atoms :   35 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_38,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_80,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_125,plain,(
    ! [B_93,A_94] :
      ( v1_relat_1(B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_94))
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_128,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9')) ),
    inference(resolution,[status(thm)],[c_80,c_125])).

tff(c_134,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_128])).

tff(c_84,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_40,plain,(
    ! [A_25,D_64] :
      ( r2_hidden(k1_funct_1(A_25,D_64),k2_relat_1(A_25))
      | ~ r2_hidden(D_64,k1_relat_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_154,plain,(
    ! [D_100,B_101,A_102] :
      ( D_100 = B_101
      | D_100 = A_102
      | ~ r2_hidden(D_100,k2_tarski(A_102,B_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_173,plain,(
    ! [D_103,A_104] :
      ( D_103 = A_104
      | D_103 = A_104
      | ~ r2_hidden(D_103,k1_tarski(A_104)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_154])).

tff(c_181,plain,(
    ! [A_104,B_2] :
      ( '#skF_1'(k1_tarski(A_104),B_2) = A_104
      | r1_tarski(k1_tarski(A_104),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_173])).

tff(c_206,plain,(
    ! [A_111,B_112,C_113] :
      ( k2_relset_1(A_111,B_112,C_113) = k2_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_214,plain,(
    k2_relset_1(k1_tarski('#skF_8'),'#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_80,c_206])).

tff(c_365,plain,(
    ! [A_140,B_141,C_142] :
      ( m1_subset_1(k2_relset_1(A_140,B_141,C_142),k1_zfmisc_1(B_141))
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_385,plain,
    ( m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1('#skF_9'))
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_365])).

tff(c_391,plain,(
    m1_subset_1(k2_relat_1('#skF_10'),k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_385])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_399,plain,(
    r1_tarski(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_391,c_32])).

tff(c_193,plain,(
    ! [C_108,B_109,A_110] :
      ( r2_hidden(C_108,B_109)
      | ~ r2_hidden(C_108,A_110)
      | ~ r1_tarski(A_110,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_301,plain,(
    ! [A_129,B_130,B_131] :
      ( r2_hidden('#skF_1'(A_129,B_130),B_131)
      | ~ r1_tarski(A_129,B_131)
      | r1_tarski(A_129,B_130) ) ),
    inference(resolution,[status(thm)],[c_6,c_193])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_715,plain,(
    ! [A_203,B_204,B_205,B_206] :
      ( r2_hidden('#skF_1'(A_203,B_204),B_205)
      | ~ r1_tarski(B_206,B_205)
      | ~ r1_tarski(A_203,B_206)
      | r1_tarski(A_203,B_204) ) ),
    inference(resolution,[status(thm)],[c_301,c_2])).

tff(c_734,plain,(
    ! [A_207,B_208] :
      ( r2_hidden('#skF_1'(A_207,B_208),'#skF_9')
      | ~ r1_tarski(A_207,k2_relat_1('#skF_10'))
      | r1_tarski(A_207,B_208) ) ),
    inference(resolution,[status(thm)],[c_399,c_715])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_752,plain,(
    ! [A_209] :
      ( ~ r1_tarski(A_209,k2_relat_1('#skF_10'))
      | r1_tarski(A_209,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_734,c_4])).

tff(c_796,plain,(
    ! [A_213] :
      ( r1_tarski(k1_tarski(A_213),'#skF_9')
      | '#skF_1'(k1_tarski(A_213),k2_relat_1('#skF_10')) = A_213 ) ),
    inference(resolution,[status(thm)],[c_181,c_752])).

tff(c_1155,plain,(
    ! [A_249] :
      ( ~ r2_hidden(A_249,k2_relat_1('#skF_10'))
      | r1_tarski(k1_tarski(A_249),k2_relat_1('#skF_10'))
      | r1_tarski(k1_tarski(A_249),'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_4])).

tff(c_751,plain,(
    ! [A_207] :
      ( ~ r1_tarski(A_207,k2_relat_1('#skF_10'))
      | r1_tarski(A_207,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_734,c_4])).

tff(c_1174,plain,(
    ! [A_250] :
      ( ~ r2_hidden(A_250,k2_relat_1('#skF_10'))
      | r1_tarski(k1_tarski(A_250),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1155,c_751])).

tff(c_1178,plain,(
    ! [D_64] :
      ( r1_tarski(k1_tarski(k1_funct_1('#skF_10',D_64)),'#skF_9')
      | ~ r2_hidden(D_64,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_40,c_1174])).

tff(c_1192,plain,(
    ! [D_251] :
      ( r1_tarski(k1_tarski(k1_funct_1('#skF_10',D_251)),'#skF_9')
      | ~ r2_hidden(D_251,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_84,c_1178])).

tff(c_88,plain,(
    ! [A_83] : k2_tarski(A_83,A_83) = k1_tarski(A_83) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [D_11,A_6] : r2_hidden(D_11,k2_tarski(A_6,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_94,plain,(
    ! [A_83] : r2_hidden(A_83,k1_tarski(A_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_10])).

tff(c_203,plain,(
    ! [A_83,B_109] :
      ( r2_hidden(A_83,B_109)
      | ~ r1_tarski(k1_tarski(A_83),B_109) ) ),
    inference(resolution,[status(thm)],[c_94,c_193])).

tff(c_1207,plain,(
    ! [D_252] :
      ( r2_hidden(k1_funct_1('#skF_10',D_252),'#skF_9')
      | ~ r2_hidden(D_252,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_1192,c_203])).

tff(c_76,plain,(
    ~ r2_hidden(k1_funct_1('#skF_10','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1217,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_1207,c_76])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_82,plain,(
    v1_funct_2('#skF_10',k1_tarski('#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_326,plain,(
    ! [A_132,B_133,C_134] :
      ( k1_relset_1(A_132,B_133,C_134) = k1_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_334,plain,(
    k1_relset_1(k1_tarski('#skF_8'),'#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_80,c_326])).

tff(c_1462,plain,(
    ! [B_276,A_277,C_278] :
      ( k1_xboole_0 = B_276
      | k1_relset_1(A_277,B_276,C_278) = A_277
      | ~ v1_funct_2(C_278,A_277,B_276)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_277,B_276))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1469,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1(k1_tarski('#skF_8'),'#skF_9','#skF_10') = k1_tarski('#skF_8')
    | ~ v1_funct_2('#skF_10',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_1462])).

tff(c_1477,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_tarski('#skF_8') = k1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_334,c_1469])).

tff(c_1478,plain,(
    k1_tarski('#skF_8') = k1_relat_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1477])).

tff(c_1530,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1478,c_94])).

tff(c_1540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1217,c_1530])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:28:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.99/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.69  
% 3.99/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.69  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.99/1.69  
% 3.99/1.69  %Foreground sorts:
% 3.99/1.69  
% 3.99/1.69  
% 3.99/1.69  %Background operators:
% 3.99/1.69  
% 3.99/1.69  
% 3.99/1.69  %Foreground operators:
% 3.99/1.69  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.99/1.69  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.99/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.99/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.99/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.99/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.99/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.99/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.99/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.99/1.69  tff('#skF_10', type, '#skF_10': $i).
% 3.99/1.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.99/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.99/1.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.99/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.99/1.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.99/1.69  tff('#skF_9', type, '#skF_9': $i).
% 3.99/1.69  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.99/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.99/1.69  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.99/1.69  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.99/1.69  tff('#skF_8', type, '#skF_8': $i).
% 3.99/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.99/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.99/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.99/1.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.99/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.99/1.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.99/1.69  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.99/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.99/1.69  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.99/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.99/1.69  
% 3.99/1.71  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.99/1.71  tff(f_117, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 3.99/1.71  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.99/1.71  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 3.99/1.71  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.99/1.71  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.99/1.71  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.99/1.71  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.99/1.71  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.99/1.71  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.99/1.71  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.99/1.71  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.99/1.71  tff(c_38, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.99/1.71  tff(c_80, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.99/1.71  tff(c_125, plain, (![B_93, A_94]: (v1_relat_1(B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_94)) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.99/1.71  tff(c_128, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9'))), inference(resolution, [status(thm)], [c_80, c_125])).
% 3.99/1.71  tff(c_134, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_128])).
% 3.99/1.71  tff(c_84, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.99/1.71  tff(c_40, plain, (![A_25, D_64]: (r2_hidden(k1_funct_1(A_25, D_64), k2_relat_1(A_25)) | ~r2_hidden(D_64, k1_relat_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.99/1.71  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.99/1.71  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.99/1.71  tff(c_154, plain, (![D_100, B_101, A_102]: (D_100=B_101 | D_100=A_102 | ~r2_hidden(D_100, k2_tarski(A_102, B_101)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.99/1.71  tff(c_173, plain, (![D_103, A_104]: (D_103=A_104 | D_103=A_104 | ~r2_hidden(D_103, k1_tarski(A_104)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_154])).
% 3.99/1.71  tff(c_181, plain, (![A_104, B_2]: ('#skF_1'(k1_tarski(A_104), B_2)=A_104 | r1_tarski(k1_tarski(A_104), B_2))), inference(resolution, [status(thm)], [c_6, c_173])).
% 3.99/1.71  tff(c_206, plain, (![A_111, B_112, C_113]: (k2_relset_1(A_111, B_112, C_113)=k2_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.99/1.71  tff(c_214, plain, (k2_relset_1(k1_tarski('#skF_8'), '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_80, c_206])).
% 3.99/1.71  tff(c_365, plain, (![A_140, B_141, C_142]: (m1_subset_1(k2_relset_1(A_140, B_141, C_142), k1_zfmisc_1(B_141)) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.99/1.71  tff(c_385, plain, (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1('#skF_9')) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_214, c_365])).
% 3.99/1.71  tff(c_391, plain, (m1_subset_1(k2_relat_1('#skF_10'), k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_385])).
% 3.99/1.71  tff(c_32, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.99/1.71  tff(c_399, plain, (r1_tarski(k2_relat_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_391, c_32])).
% 3.99/1.71  tff(c_193, plain, (![C_108, B_109, A_110]: (r2_hidden(C_108, B_109) | ~r2_hidden(C_108, A_110) | ~r1_tarski(A_110, B_109))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.99/1.71  tff(c_301, plain, (![A_129, B_130, B_131]: (r2_hidden('#skF_1'(A_129, B_130), B_131) | ~r1_tarski(A_129, B_131) | r1_tarski(A_129, B_130))), inference(resolution, [status(thm)], [c_6, c_193])).
% 3.99/1.71  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.99/1.71  tff(c_715, plain, (![A_203, B_204, B_205, B_206]: (r2_hidden('#skF_1'(A_203, B_204), B_205) | ~r1_tarski(B_206, B_205) | ~r1_tarski(A_203, B_206) | r1_tarski(A_203, B_204))), inference(resolution, [status(thm)], [c_301, c_2])).
% 3.99/1.71  tff(c_734, plain, (![A_207, B_208]: (r2_hidden('#skF_1'(A_207, B_208), '#skF_9') | ~r1_tarski(A_207, k2_relat_1('#skF_10')) | r1_tarski(A_207, B_208))), inference(resolution, [status(thm)], [c_399, c_715])).
% 3.99/1.71  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.99/1.71  tff(c_752, plain, (![A_209]: (~r1_tarski(A_209, k2_relat_1('#skF_10')) | r1_tarski(A_209, '#skF_9'))), inference(resolution, [status(thm)], [c_734, c_4])).
% 3.99/1.71  tff(c_796, plain, (![A_213]: (r1_tarski(k1_tarski(A_213), '#skF_9') | '#skF_1'(k1_tarski(A_213), k2_relat_1('#skF_10'))=A_213)), inference(resolution, [status(thm)], [c_181, c_752])).
% 3.99/1.71  tff(c_1155, plain, (![A_249]: (~r2_hidden(A_249, k2_relat_1('#skF_10')) | r1_tarski(k1_tarski(A_249), k2_relat_1('#skF_10')) | r1_tarski(k1_tarski(A_249), '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_796, c_4])).
% 3.99/1.71  tff(c_751, plain, (![A_207]: (~r1_tarski(A_207, k2_relat_1('#skF_10')) | r1_tarski(A_207, '#skF_9'))), inference(resolution, [status(thm)], [c_734, c_4])).
% 3.99/1.71  tff(c_1174, plain, (![A_250]: (~r2_hidden(A_250, k2_relat_1('#skF_10')) | r1_tarski(k1_tarski(A_250), '#skF_9'))), inference(resolution, [status(thm)], [c_1155, c_751])).
% 3.99/1.71  tff(c_1178, plain, (![D_64]: (r1_tarski(k1_tarski(k1_funct_1('#skF_10', D_64)), '#skF_9') | ~r2_hidden(D_64, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_40, c_1174])).
% 3.99/1.71  tff(c_1192, plain, (![D_251]: (r1_tarski(k1_tarski(k1_funct_1('#skF_10', D_251)), '#skF_9') | ~r2_hidden(D_251, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_84, c_1178])).
% 3.99/1.71  tff(c_88, plain, (![A_83]: (k2_tarski(A_83, A_83)=k1_tarski(A_83))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.99/1.71  tff(c_10, plain, (![D_11, A_6]: (r2_hidden(D_11, k2_tarski(A_6, D_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.99/1.71  tff(c_94, plain, (![A_83]: (r2_hidden(A_83, k1_tarski(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_10])).
% 3.99/1.71  tff(c_203, plain, (![A_83, B_109]: (r2_hidden(A_83, B_109) | ~r1_tarski(k1_tarski(A_83), B_109))), inference(resolution, [status(thm)], [c_94, c_193])).
% 3.99/1.71  tff(c_1207, plain, (![D_252]: (r2_hidden(k1_funct_1('#skF_10', D_252), '#skF_9') | ~r2_hidden(D_252, k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_1192, c_203])).
% 3.99/1.71  tff(c_76, plain, (~r2_hidden(k1_funct_1('#skF_10', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.99/1.71  tff(c_1217, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_1207, c_76])).
% 3.99/1.71  tff(c_78, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.99/1.71  tff(c_82, plain, (v1_funct_2('#skF_10', k1_tarski('#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.99/1.71  tff(c_326, plain, (![A_132, B_133, C_134]: (k1_relset_1(A_132, B_133, C_134)=k1_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.99/1.71  tff(c_334, plain, (k1_relset_1(k1_tarski('#skF_8'), '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_80, c_326])).
% 3.99/1.71  tff(c_1462, plain, (![B_276, A_277, C_278]: (k1_xboole_0=B_276 | k1_relset_1(A_277, B_276, C_278)=A_277 | ~v1_funct_2(C_278, A_277, B_276) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_277, B_276))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.99/1.71  tff(c_1469, plain, (k1_xboole_0='#skF_9' | k1_relset_1(k1_tarski('#skF_8'), '#skF_9', '#skF_10')=k1_tarski('#skF_8') | ~v1_funct_2('#skF_10', k1_tarski('#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_80, c_1462])).
% 3.99/1.71  tff(c_1477, plain, (k1_xboole_0='#skF_9' | k1_tarski('#skF_8')=k1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_334, c_1469])).
% 3.99/1.71  tff(c_1478, plain, (k1_tarski('#skF_8')=k1_relat_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_78, c_1477])).
% 3.99/1.71  tff(c_1530, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1478, c_94])).
% 3.99/1.71  tff(c_1540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1217, c_1530])).
% 3.99/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.71  
% 3.99/1.71  Inference rules
% 3.99/1.71  ----------------------
% 3.99/1.71  #Ref     : 0
% 3.99/1.71  #Sup     : 320
% 3.99/1.71  #Fact    : 0
% 3.99/1.71  #Define  : 0
% 3.99/1.71  #Split   : 3
% 3.99/1.71  #Chain   : 0
% 3.99/1.71  #Close   : 0
% 3.99/1.71  
% 3.99/1.71  Ordering : KBO
% 3.99/1.71  
% 3.99/1.71  Simplification rules
% 3.99/1.71  ----------------------
% 3.99/1.71  #Subsume      : 62
% 3.99/1.71  #Demod        : 77
% 3.99/1.71  #Tautology    : 78
% 3.99/1.71  #SimpNegUnit  : 2
% 3.99/1.71  #BackRed      : 14
% 3.99/1.71  
% 3.99/1.71  #Partial instantiations: 0
% 3.99/1.71  #Strategies tried      : 1
% 3.99/1.71  
% 3.99/1.71  Timing (in seconds)
% 3.99/1.71  ----------------------
% 3.99/1.71  Preprocessing        : 0.35
% 3.99/1.71  Parsing              : 0.17
% 3.99/1.71  CNF conversion       : 0.03
% 3.99/1.71  Main loop            : 0.55
% 3.99/1.71  Inferencing          : 0.20
% 3.99/1.71  Reduction            : 0.17
% 3.99/1.71  Demodulation         : 0.11
% 3.99/1.71  BG Simplification    : 0.03
% 3.99/1.71  Subsumption          : 0.12
% 3.99/1.71  Abstraction          : 0.03
% 3.99/1.71  MUC search           : 0.00
% 3.99/1.71  Cooper               : 0.00
% 3.99/1.71  Total                : 0.94
% 3.99/1.71  Index Insertion      : 0.00
% 3.99/1.71  Index Deletion       : 0.00
% 3.99/1.71  Index Matching       : 0.00
% 3.99/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
