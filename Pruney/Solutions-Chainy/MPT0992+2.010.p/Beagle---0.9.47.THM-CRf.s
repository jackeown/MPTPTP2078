%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:32 EST 2020

% Result     : Theorem 17.41s
% Output     : CNFRefutation 17.62s
% Verified   : 
% Statistics : Number of formulae       :  230 (3337 expanded)
%              Number of leaves         :   36 (1019 expanded)
%              Depth                    :   18
%              Number of atoms          :  405 (8743 expanded)
%              Number of equality atoms :  104 (2286 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_56,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_535,plain,(
    ! [C_123,A_124,B_125] :
      ( v1_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_544,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_535])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_36279,plain,(
    ! [A_1239,B_1240,C_1241] :
      ( k1_relset_1(A_1239,B_1240,C_1241) = k1_relat_1(C_1241)
      | ~ m1_subset_1(C_1241,k1_zfmisc_1(k2_zfmisc_1(A_1239,B_1240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36292,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_36279])).

tff(c_36764,plain,(
    ! [B_1293,A_1294,C_1295] :
      ( k1_xboole_0 = B_1293
      | k1_relset_1(A_1294,B_1293,C_1295) = A_1294
      | ~ v1_funct_2(C_1295,A_1294,B_1293)
      | ~ m1_subset_1(C_1295,k1_zfmisc_1(k2_zfmisc_1(A_1294,B_1293))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36777,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_36764])).

tff(c_36785,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_36292,c_36777])).

tff(c_36786,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_36785])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,A_13)) = A_13
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_36801,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36786,c_18])).

tff(c_36823,plain,(
    ! [A_1297] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_1297)) = A_1297
      | ~ r1_tarski(A_1297,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_36801])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_36577,plain,(
    ! [A_1283,B_1284,C_1285,D_1286] :
      ( k2_partfun1(A_1283,B_1284,C_1285,D_1286) = k7_relat_1(C_1285,D_1286)
      | ~ m1_subset_1(C_1285,k1_zfmisc_1(k2_zfmisc_1(A_1283,B_1284)))
      | ~ v1_funct_1(C_1285) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36586,plain,(
    ! [D_1286] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_1286) = k7_relat_1('#skF_4',D_1286)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_36577])).

tff(c_36594,plain,(
    ! [D_1286] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_1286) = k7_relat_1('#skF_4',D_1286) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_36586])).

tff(c_1165,plain,(
    ! [A_220,B_221,C_222,D_223] :
      ( k2_partfun1(A_220,B_221,C_222,D_223) = k7_relat_1(C_222,D_223)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221)))
      | ~ v1_funct_1(C_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1172,plain,(
    ! [D_223] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_223) = k7_relat_1('#skF_4',D_223)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_1165])).

tff(c_1177,plain,(
    ! [D_223] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_223) = k7_relat_1('#skF_4',D_223) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1172])).

tff(c_1506,plain,(
    ! [A_249,B_250,C_251,D_252] :
      ( m1_subset_1(k2_partfun1(A_249,B_250,C_251,D_252),k1_zfmisc_1(k2_zfmisc_1(A_249,B_250)))
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250)))
      | ~ v1_funct_1(C_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1549,plain,(
    ! [D_223] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_223),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1177,c_1506])).

tff(c_1565,plain,(
    ! [D_253] : m1_subset_1(k7_relat_1('#skF_4',D_253),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_1549])).

tff(c_22,plain,(
    ! [C_20,B_19,A_18] :
      ( v5_relat_1(C_20,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1610,plain,(
    ! [D_253] : v5_relat_1(k7_relat_1('#skF_4',D_253),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1565,c_22])).

tff(c_20,plain,(
    ! [C_17,A_15,B_16] :
      ( v1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1612,plain,(
    ! [D_253] : v1_relat_1(k7_relat_1('#skF_4',D_253)) ),
    inference(resolution,[status(thm)],[c_1565,c_20])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_957,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( v1_funct_1(k2_partfun1(A_194,B_195,C_196,D_197))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195)))
      | ~ v1_funct_1(C_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_962,plain,(
    ! [D_197] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_197))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_957])).

tff(c_966,plain,(
    ! [D_197] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_197)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_962])).

tff(c_1178,plain,(
    ! [D_197] : v1_funct_1(k7_relat_1('#skF_4',D_197)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1177,c_966])).

tff(c_810,plain,(
    ! [A_161,B_162,C_163] :
      ( k1_relset_1(A_161,B_162,C_163) = k1_relat_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_819,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_810])).

tff(c_1213,plain,(
    ! [B_228,A_229,C_230] :
      ( k1_xboole_0 = B_228
      | k1_relset_1(A_229,B_228,C_230) = A_229
      | ~ v1_funct_2(C_230,A_229,B_228)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_229,B_228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1223,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_1213])).

tff(c_1228,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_819,c_1223])).

tff(c_1229,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1228])).

tff(c_1247,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1229,c_18])).

tff(c_1276,plain,(
    ! [A_232] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_232)) = A_232
      | ~ r1_tarski(A_232,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_1247])).

tff(c_987,plain,(
    ! [B_203,A_204] :
      ( m1_subset_1(B_203,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_203),A_204)))
      | ~ r1_tarski(k2_relat_1(B_203),A_204)
      | ~ v1_funct_1(B_203)
      | ~ v1_relat_1(B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(A_2,B_3)
      | ~ m1_subset_1(A_2,k1_zfmisc_1(B_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1025,plain,(
    ! [B_203,A_204] :
      ( r1_tarski(B_203,k2_zfmisc_1(k1_relat_1(B_203),A_204))
      | ~ r1_tarski(k2_relat_1(B_203),A_204)
      | ~ v1_funct_1(B_203)
      | ~ v1_relat_1(B_203) ) ),
    inference(resolution,[status(thm)],[c_987,c_4])).

tff(c_1282,plain,(
    ! [A_232,A_204] :
      ( r1_tarski(k7_relat_1('#skF_4',A_232),k2_zfmisc_1(A_232,A_204))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_232)),A_204)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_232))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_232))
      | ~ r1_tarski(A_232,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1276,c_1025])).

tff(c_1308,plain,(
    ! [A_232,A_204] :
      ( r1_tarski(k7_relat_1('#skF_4',A_232),k2_zfmisc_1(A_232,A_204))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_232)),A_204)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_232))
      | ~ r1_tarski(A_232,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_1282])).

tff(c_35903,plain,(
    ! [A_1208,A_1209] :
      ( r1_tarski(k7_relat_1('#skF_4',A_1208),k2_zfmisc_1(A_1208,A_1209))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_1208)),A_1209)
      | ~ r1_tarski(A_1208,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1612,c_1308])).

tff(c_35911,plain,(
    ! [A_1208,A_7] :
      ( r1_tarski(k7_relat_1('#skF_4',A_1208),k2_zfmisc_1(A_1208,A_7))
      | ~ r1_tarski(A_1208,'#skF_1')
      | ~ v5_relat_1(k7_relat_1('#skF_4',A_1208),A_7)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_1208)) ) ),
    inference(resolution,[status(thm)],[c_12,c_35903])).

tff(c_35922,plain,(
    ! [A_1210,A_1211] :
      ( r1_tarski(k7_relat_1('#skF_4',A_1210),k2_zfmisc_1(A_1210,A_1211))
      | ~ r1_tarski(A_1210,'#skF_1')
      | ~ v5_relat_1(k7_relat_1('#skF_4',A_1210),A_1211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1612,c_35911])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_514,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( v1_funct_1(k2_partfun1(A_115,B_116,C_117,D_118))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_519,plain,(
    ! [D_118] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_118))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_514])).

tff(c_523,plain,(
    ! [D_118] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_118)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_519])).

tff(c_52,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_70,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_70])).

tff(c_527,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_645,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_527])).

tff(c_725,plain,(
    ~ r1_tarski(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_645])).

tff(c_1179,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1177,c_725])).

tff(c_35944,plain,
    ( ~ r1_tarski('#skF_3','#skF_1')
    | ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_35922,c_1179])).

tff(c_35996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1610,c_56,c_35944])).

tff(c_35998,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_527])).

tff(c_36290,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_35998,c_36279])).

tff(c_36599,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36594,c_36594,c_36290])).

tff(c_35997,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_527])).

tff(c_36606,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36594,c_35997])).

tff(c_36605,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36594,c_35998])).

tff(c_34,plain,(
    ! [B_25,C_26,A_24] :
      ( k1_xboole_0 = B_25
      | v1_funct_2(C_26,A_24,B_25)
      | k1_relset_1(A_24,B_25,C_26) != A_24
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36693,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_36605,c_34])).

tff(c_36718,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_36606,c_64,c_36693])).

tff(c_36737,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36599,c_36718])).

tff(c_36832,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_36823,c_36737])).

tff(c_36862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_36832])).

tff(c_36863,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36865,plain,(
    ! [A_1] : r1_tarski('#skF_1',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36863,c_2])).

tff(c_37375,plain,(
    ! [B_1367,A_1368] :
      ( v1_relat_1(B_1367)
      | ~ m1_subset_1(B_1367,k1_zfmisc_1(A_1368))
      | ~ v1_relat_1(A_1368) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_37385,plain,(
    ! [A_1369,B_1370] :
      ( v1_relat_1(A_1369)
      | ~ v1_relat_1(B_1370)
      | ~ r1_tarski(A_1369,B_1370) ) ),
    inference(resolution,[status(thm)],[c_6,c_37375])).

tff(c_37400,plain,(
    ! [A_1] :
      ( v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_36865,c_37385])).

tff(c_37402,plain,(
    ! [A_1] : ~ v1_relat_1(A_1) ),
    inference(splitLeft,[status(thm)],[c_37400])).

tff(c_37407,plain,(
    ! [C_17,A_15,B_16] : ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ),
    inference(negUnitSimplification,[status(thm)],[c_37402,c_20])).

tff(c_36864,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_36870,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36863,c_36864])).

tff(c_36877,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36870,c_58])).

tff(c_37409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37407,c_36877])).

tff(c_37410,plain,(
    v1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_37400])).

tff(c_38374,plain,(
    ! [C_1487,A_1488,B_1489] :
      ( v4_relat_1(C_1487,A_1488)
      | ~ m1_subset_1(C_1487,k1_zfmisc_1(k2_zfmisc_1(A_1488,B_1489))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38410,plain,(
    ! [A_1490,A_1491,B_1492] :
      ( v4_relat_1(A_1490,A_1491)
      | ~ r1_tarski(A_1490,k2_zfmisc_1(A_1491,B_1492)) ) ),
    inference(resolution,[status(thm)],[c_6,c_38374])).

tff(c_38426,plain,(
    ! [A_1493] : v4_relat_1('#skF_1',A_1493) ),
    inference(resolution,[status(thm)],[c_36865,c_38410])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38429,plain,(
    ! [A_1493] :
      ( k7_relat_1('#skF_1',A_1493) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38426,c_14])).

tff(c_38432,plain,(
    ! [A_1493] : k7_relat_1('#skF_1',A_1493) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37410,c_38429])).

tff(c_38528,plain,(
    ! [B_1506,A_1507] :
      ( k1_relat_1(k7_relat_1(B_1506,A_1507)) = A_1507
      | ~ r1_tarski(A_1507,k1_relat_1(B_1506))
      | ~ v1_relat_1(B_1506) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_38544,plain,(
    ! [B_1508] :
      ( k1_relat_1(k7_relat_1(B_1508,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_1508) ) ),
    inference(resolution,[status(thm)],[c_36865,c_38528])).

tff(c_38557,plain,
    ( k1_relat_1('#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38432,c_38544])).

tff(c_38564,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37410,c_38557])).

tff(c_38579,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_1',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38564,c_18])).

tff(c_38605,plain,(
    ! [A_1509] :
      ( A_1509 = '#skF_1'
      | ~ r1_tarski(A_1509,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37410,c_38564,c_38432,c_38579])).

tff(c_38627,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_56,c_38605])).

tff(c_37415,plain,(
    ! [C_1374,A_1375,B_1376] :
      ( v1_relat_1(C_1374)
      | ~ m1_subset_1(C_1374,k1_zfmisc_1(k2_zfmisc_1(A_1375,B_1376))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_37424,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36877,c_37415])).

tff(c_37443,plain,(
    ! [C_1382,B_1383,A_1384] :
      ( v5_relat_1(C_1382,B_1383)
      | ~ m1_subset_1(C_1382,k1_zfmisc_1(k2_zfmisc_1(A_1384,B_1383))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_37452,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_36877,c_37443])).

tff(c_37453,plain,(
    ! [C_1385,A_1386,B_1387] :
      ( v4_relat_1(C_1385,A_1386)
      | ~ m1_subset_1(C_1385,k1_zfmisc_1(k2_zfmisc_1(A_1386,B_1387))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_37463,plain,(
    ! [A_1388,A_1389,B_1390] :
      ( v4_relat_1(A_1388,A_1389)
      | ~ r1_tarski(A_1388,k2_zfmisc_1(A_1389,B_1390)) ) ),
    inference(resolution,[status(thm)],[c_6,c_37453])).

tff(c_37478,plain,(
    ! [A_1389] : v4_relat_1('#skF_1',A_1389) ),
    inference(resolution,[status(thm)],[c_36865,c_37463])).

tff(c_37501,plain,(
    ! [B_1396,A_1397] :
      ( k7_relat_1(B_1396,A_1397) = B_1396
      | ~ v4_relat_1(B_1396,A_1397)
      | ~ v1_relat_1(B_1396) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_37504,plain,(
    ! [A_1389] :
      ( k7_relat_1('#skF_1',A_1389) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_37478,c_37501])).

tff(c_37510,plain,(
    ! [A_1389] : k7_relat_1('#skF_1',A_1389) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37410,c_37504])).

tff(c_37575,plain,(
    ! [B_1401,A_1402] :
      ( k1_relat_1(k7_relat_1(B_1401,A_1402)) = A_1402
      | ~ r1_tarski(A_1402,k1_relat_1(B_1401))
      | ~ v1_relat_1(B_1401) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_37591,plain,(
    ! [B_1403] :
      ( k1_relat_1(k7_relat_1(B_1403,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_1403) ) ),
    inference(resolution,[status(thm)],[c_36865,c_37575])).

tff(c_37604,plain,
    ( k1_relat_1('#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_37510,c_37591])).

tff(c_37611,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37410,c_37604])).

tff(c_37626,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_1',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37611,c_18])).

tff(c_37632,plain,(
    ! [A_1404] :
      ( A_1404 = '#skF_1'
      | ~ r1_tarski(A_1404,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37410,c_37611,c_37510,c_37626])).

tff(c_37710,plain,(
    ! [B_1408] :
      ( k2_relat_1(B_1408) = '#skF_1'
      | ~ v5_relat_1(B_1408,'#skF_1')
      | ~ v1_relat_1(B_1408) ) ),
    inference(resolution,[status(thm)],[c_12,c_37632])).

tff(c_37717,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_37452,c_37710])).

tff(c_37723,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37424,c_37717])).

tff(c_37462,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_36877,c_37453])).

tff(c_37507,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_37462,c_37501])).

tff(c_37513,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37424,c_37507])).

tff(c_37607,plain,
    ( k1_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_37513,c_37591])).

tff(c_37613,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37424,c_37607])).

tff(c_38099,plain,(
    ! [B_1466,A_1467] :
      ( m1_subset_1(B_1466,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1466),A_1467)))
      | ~ r1_tarski(k2_relat_1(B_1466),A_1467)
      | ~ v1_funct_1(B_1466)
      | ~ v1_relat_1(B_1466) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38135,plain,(
    ! [A_1467] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_1467)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_1467)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37613,c_38099])).

tff(c_38152,plain,(
    ! [A_1468] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_1468))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37424,c_62,c_36865,c_37723,c_38135])).

tff(c_38205,plain,(
    ! [A_1468] : r1_tarski('#skF_4',k2_zfmisc_1('#skF_1',A_1468)) ),
    inference(resolution,[status(thm)],[c_38152,c_4])).

tff(c_38150,plain,(
    ! [A_1467] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_1467))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37424,c_62,c_36865,c_37723,c_38135])).

tff(c_38206,plain,(
    ! [A_1469,B_1470,C_1471,D_1472] :
      ( k2_partfun1(A_1469,B_1470,C_1471,D_1472) = k7_relat_1(C_1471,D_1472)
      | ~ m1_subset_1(C_1471,k1_zfmisc_1(k2_zfmisc_1(A_1469,B_1470)))
      | ~ v1_funct_1(C_1471) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_38208,plain,(
    ! [A_1467,D_1472] :
      ( k2_partfun1('#skF_1',A_1467,'#skF_4',D_1472) = k7_relat_1('#skF_4',D_1472)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38150,c_38206])).

tff(c_38216,plain,(
    ! [A_1467,D_1472] : k2_partfun1('#skF_1',A_1467,'#skF_4',D_1472) = k7_relat_1('#skF_4',D_1472) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_38208])).

tff(c_37654,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_56,c_37632])).

tff(c_37360,plain,(
    ! [A_1363,B_1364,C_1365,D_1366] :
      ( v1_funct_1(k2_partfun1(A_1363,B_1364,C_1365,D_1366))
      | ~ m1_subset_1(C_1365,k1_zfmisc_1(k2_zfmisc_1(A_1363,B_1364)))
      | ~ v1_funct_1(C_1365) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_37365,plain,(
    ! [D_1366] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4',D_1366))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36877,c_37360])).

tff(c_37369,plain,(
    ! [D_1366] : v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4',D_1366)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_37365])).

tff(c_36891,plain,(
    ! [B_1305,A_1306] :
      ( v1_relat_1(B_1305)
      | ~ m1_subset_1(B_1305,k1_zfmisc_1(A_1306))
      | ~ v1_relat_1(A_1306) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36901,plain,(
    ! [A_1307,B_1308] :
      ( v1_relat_1(A_1307)
      | ~ v1_relat_1(B_1308)
      | ~ r1_tarski(A_1307,B_1308) ) ),
    inference(resolution,[status(thm)],[c_6,c_36891])).

tff(c_36916,plain,(
    ! [A_1] :
      ( v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_36865,c_36901])).

tff(c_36928,plain,(
    ! [A_1] : ~ v1_relat_1(A_1) ),
    inference(splitLeft,[status(thm)],[c_36916])).

tff(c_36918,plain,(
    ! [C_1309,A_1310,B_1311] :
      ( v1_relat_1(C_1309)
      | ~ m1_subset_1(C_1309,k1_zfmisc_1(k2_zfmisc_1(A_1310,B_1311))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36927,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36877,c_36918])).

tff(c_36933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36928,c_36927])).

tff(c_36934,plain,(
    v1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_36916])).

tff(c_37007,plain,(
    ! [C_1330,A_1331,B_1332] :
      ( v4_relat_1(C_1330,A_1331)
      | ~ m1_subset_1(C_1330,k1_zfmisc_1(k2_zfmisc_1(A_1331,B_1332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_37094,plain,(
    ! [A_1338,A_1339,B_1340] :
      ( v4_relat_1(A_1338,A_1339)
      | ~ r1_tarski(A_1338,k2_zfmisc_1(A_1339,B_1340)) ) ),
    inference(resolution,[status(thm)],[c_6,c_37007])).

tff(c_37115,plain,(
    ! [A_1341] : v4_relat_1('#skF_1',A_1341) ),
    inference(resolution,[status(thm)],[c_36865,c_37094])).

tff(c_37118,plain,(
    ! [A_1341] :
      ( k7_relat_1('#skF_1',A_1341) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_37115,c_14])).

tff(c_37133,plain,(
    ! [A_1345] : k7_relat_1('#skF_1',A_1345) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36934,c_37118])).

tff(c_37017,plain,(
    ! [B_1333,A_1334] :
      ( k1_relat_1(k7_relat_1(B_1333,A_1334)) = A_1334
      | ~ r1_tarski(A_1334,k1_relat_1(B_1333))
      | ~ v1_relat_1(B_1333) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_37032,plain,(
    ! [B_1333] :
      ( k1_relat_1(k7_relat_1(B_1333,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_1333) ) ),
    inference(resolution,[status(thm)],[c_36865,c_37017])).

tff(c_37139,plain,
    ( k1_relat_1('#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_37133,c_37032])).

tff(c_37150,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36934,c_37139])).

tff(c_37121,plain,(
    ! [A_1341] : k7_relat_1('#skF_1',A_1341) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36934,c_37118])).

tff(c_37159,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_1',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37150,c_18])).

tff(c_37200,plain,(
    ! [A_1347] :
      ( A_1347 = '#skF_1'
      | ~ r1_tarski(A_1347,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36934,c_37150,c_37121,c_37159])).

tff(c_37222,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_56,c_37200])).

tff(c_36889,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36870,c_36870,c_36870,c_36870,c_36870,c_52])).

tff(c_36890,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_36889])).

tff(c_37224,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37222,c_36890])).

tff(c_37372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37369,c_37224])).

tff(c_37373,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_36889])).

tff(c_37414,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_37373])).

tff(c_37482,plain,(
    ~ r1_tarski(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_37414])).

tff(c_37655,plain,(
    ~ r1_tarski(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37654,c_37654,c_37482])).

tff(c_38339,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38216,c_37655])).

tff(c_38343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38205,c_37513,c_38339])).

tff(c_38345,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_37373])).

tff(c_38497,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38345,c_20])).

tff(c_38631,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38627,c_38497])).

tff(c_39018,plain,(
    ! [A_1544,B_1545,C_1546,D_1547] :
      ( v1_funct_1(k2_partfun1(A_1544,B_1545,C_1546,D_1547))
      | ~ m1_subset_1(C_1546,k1_zfmisc_1(k2_zfmisc_1(A_1544,B_1545)))
      | ~ v1_funct_1(C_1546) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_39025,plain,(
    ! [D_1547] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4',D_1547))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36877,c_39018])).

tff(c_39032,plain,(
    ! [D_1547] : v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4',D_1547)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_39025])).

tff(c_38495,plain,(
    v5_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_38345,c_22])).

tff(c_38630,plain,(
    v5_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38627,c_38495])).

tff(c_38689,plain,(
    ! [B_1513] :
      ( k2_relat_1(B_1513) = '#skF_1'
      | ~ v5_relat_1(B_1513,'#skF_1')
      | ~ v1_relat_1(B_1513) ) ),
    inference(resolution,[status(thm)],[c_12,c_38605])).

tff(c_38692,plain,
    ( k2_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_38630,c_38689])).

tff(c_38702,plain,(
    k2_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38631,c_38692])).

tff(c_24,plain,(
    ! [C_20,A_18,B_19] :
      ( v4_relat_1(C_20,A_18)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38496,plain,(
    v4_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_38345,c_24])).

tff(c_38502,plain,
    ( k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3') = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38496,c_14])).

tff(c_38505,plain,(
    k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3') = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38497,c_38502])).

tff(c_38998,plain,(
    k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1') = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38627,c_38627,c_38627,c_38505])).

tff(c_38543,plain,(
    ! [B_1506] :
      ( k1_relat_1(k7_relat_1(B_1506,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_1506) ) ),
    inference(resolution,[status(thm)],[c_36865,c_38528])).

tff(c_39002,plain,
    ( k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38998,c_38543])).

tff(c_39012,plain,(
    k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38631,c_39002])).

tff(c_48,plain,(
    ! [B_36,A_35] :
      ( v1_funct_2(B_36,k1_relat_1(B_36),A_35)
      | ~ r1_tarski(k2_relat_1(B_36),A_35)
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_39039,plain,(
    ! [A_35] :
      ( v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',A_35)
      | ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')),A_35)
      | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'))
      | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39012,c_48])).

tff(c_39046,plain,(
    ! [A_35] : v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38631,c_39032,c_36865,c_38702,c_39039])).

tff(c_38344,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_37373])).

tff(c_38633,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38627,c_38627,c_38344])).

tff(c_39052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39046,c_38633])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.41/8.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.41/8.35  
% 17.41/8.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.41/8.35  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 17.41/8.35  
% 17.41/8.35  %Foreground sorts:
% 17.41/8.35  
% 17.41/8.35  
% 17.41/8.35  %Background operators:
% 17.41/8.35  
% 17.41/8.35  
% 17.41/8.35  %Foreground operators:
% 17.41/8.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 17.41/8.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.41/8.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 17.41/8.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.41/8.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.41/8.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 17.41/8.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 17.41/8.35  tff('#skF_2', type, '#skF_2': $i).
% 17.41/8.35  tff('#skF_3', type, '#skF_3': $i).
% 17.41/8.35  tff('#skF_1', type, '#skF_1': $i).
% 17.41/8.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 17.41/8.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 17.41/8.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.41/8.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.41/8.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.41/8.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.41/8.35  tff('#skF_4', type, '#skF_4': $i).
% 17.41/8.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.41/8.35  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 17.41/8.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 17.41/8.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 17.41/8.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.41/8.35  
% 17.62/8.38  tff(f_138, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 17.62/8.38  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 17.62/8.38  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 17.62/8.38  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 17.62/8.38  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 17.62/8.38  tff(f_106, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 17.62/8.38  tff(f_100, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 17.62/8.38  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 17.62/8.38  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 17.62/8.38  tff(f_118, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 17.62/8.38  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 17.62/8.38  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 17.62/8.38  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 17.62/8.38  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 17.62/8.38  tff(c_56, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 17.62/8.38  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 17.62/8.38  tff(c_535, plain, (![C_123, A_124, B_125]: (v1_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 17.62/8.38  tff(c_544, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_535])).
% 17.62/8.38  tff(c_54, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_138])).
% 17.62/8.38  tff(c_64, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_54])).
% 17.62/8.38  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 17.62/8.38  tff(c_36279, plain, (![A_1239, B_1240, C_1241]: (k1_relset_1(A_1239, B_1240, C_1241)=k1_relat_1(C_1241) | ~m1_subset_1(C_1241, k1_zfmisc_1(k2_zfmisc_1(A_1239, B_1240))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 17.62/8.38  tff(c_36292, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_36279])).
% 17.62/8.38  tff(c_36764, plain, (![B_1293, A_1294, C_1295]: (k1_xboole_0=B_1293 | k1_relset_1(A_1294, B_1293, C_1295)=A_1294 | ~v1_funct_2(C_1295, A_1294, B_1293) | ~m1_subset_1(C_1295, k1_zfmisc_1(k2_zfmisc_1(A_1294, B_1293))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.62/8.38  tff(c_36777, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_36764])).
% 17.62/8.38  tff(c_36785, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_36292, c_36777])).
% 17.62/8.38  tff(c_36786, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_64, c_36785])).
% 17.62/8.38  tff(c_18, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, A_13))=A_13 | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 17.62/8.38  tff(c_36801, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_36786, c_18])).
% 17.62/8.38  tff(c_36823, plain, (![A_1297]: (k1_relat_1(k7_relat_1('#skF_4', A_1297))=A_1297 | ~r1_tarski(A_1297, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_544, c_36801])).
% 17.62/8.38  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 17.62/8.38  tff(c_36577, plain, (![A_1283, B_1284, C_1285, D_1286]: (k2_partfun1(A_1283, B_1284, C_1285, D_1286)=k7_relat_1(C_1285, D_1286) | ~m1_subset_1(C_1285, k1_zfmisc_1(k2_zfmisc_1(A_1283, B_1284))) | ~v1_funct_1(C_1285))), inference(cnfTransformation, [status(thm)], [f_106])).
% 17.62/8.38  tff(c_36586, plain, (![D_1286]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1286)=k7_relat_1('#skF_4', D_1286) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_36577])).
% 17.62/8.38  tff(c_36594, plain, (![D_1286]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1286)=k7_relat_1('#skF_4', D_1286))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_36586])).
% 17.62/8.38  tff(c_1165, plain, (![A_220, B_221, C_222, D_223]: (k2_partfun1(A_220, B_221, C_222, D_223)=k7_relat_1(C_222, D_223) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))) | ~v1_funct_1(C_222))), inference(cnfTransformation, [status(thm)], [f_106])).
% 17.62/8.38  tff(c_1172, plain, (![D_223]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_223)=k7_relat_1('#skF_4', D_223) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_1165])).
% 17.62/8.38  tff(c_1177, plain, (![D_223]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_223)=k7_relat_1('#skF_4', D_223))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1172])).
% 17.62/8.38  tff(c_1506, plain, (![A_249, B_250, C_251, D_252]: (m1_subset_1(k2_partfun1(A_249, B_250, C_251, D_252), k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))) | ~v1_funct_1(C_251))), inference(cnfTransformation, [status(thm)], [f_100])).
% 17.62/8.38  tff(c_1549, plain, (![D_223]: (m1_subset_1(k7_relat_1('#skF_4', D_223), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1177, c_1506])).
% 17.62/8.38  tff(c_1565, plain, (![D_253]: (m1_subset_1(k7_relat_1('#skF_4', D_253), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_1549])).
% 17.62/8.38  tff(c_22, plain, (![C_20, B_19, A_18]: (v5_relat_1(C_20, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 17.62/8.38  tff(c_1610, plain, (![D_253]: (v5_relat_1(k7_relat_1('#skF_4', D_253), '#skF_2'))), inference(resolution, [status(thm)], [c_1565, c_22])).
% 17.62/8.38  tff(c_20, plain, (![C_17, A_15, B_16]: (v1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 17.62/8.38  tff(c_1612, plain, (![D_253]: (v1_relat_1(k7_relat_1('#skF_4', D_253)))), inference(resolution, [status(thm)], [c_1565, c_20])).
% 17.62/8.38  tff(c_12, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 17.62/8.38  tff(c_957, plain, (![A_194, B_195, C_196, D_197]: (v1_funct_1(k2_partfun1(A_194, B_195, C_196, D_197)) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))) | ~v1_funct_1(C_196))), inference(cnfTransformation, [status(thm)], [f_100])).
% 17.62/8.38  tff(c_962, plain, (![D_197]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_197)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_957])).
% 17.62/8.38  tff(c_966, plain, (![D_197]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_197)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_962])).
% 17.62/8.38  tff(c_1178, plain, (![D_197]: (v1_funct_1(k7_relat_1('#skF_4', D_197)))), inference(demodulation, [status(thm), theory('equality')], [c_1177, c_966])).
% 17.62/8.38  tff(c_810, plain, (![A_161, B_162, C_163]: (k1_relset_1(A_161, B_162, C_163)=k1_relat_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 17.62/8.38  tff(c_819, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_810])).
% 17.62/8.38  tff(c_1213, plain, (![B_228, A_229, C_230]: (k1_xboole_0=B_228 | k1_relset_1(A_229, B_228, C_230)=A_229 | ~v1_funct_2(C_230, A_229, B_228) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_229, B_228))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.62/8.38  tff(c_1223, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_1213])).
% 17.62/8.38  tff(c_1228, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_819, c_1223])).
% 17.62/8.38  tff(c_1229, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_64, c_1228])).
% 17.62/8.38  tff(c_1247, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1229, c_18])).
% 17.62/8.38  tff(c_1276, plain, (![A_232]: (k1_relat_1(k7_relat_1('#skF_4', A_232))=A_232 | ~r1_tarski(A_232, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_544, c_1247])).
% 17.62/8.38  tff(c_987, plain, (![B_203, A_204]: (m1_subset_1(B_203, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_203), A_204))) | ~r1_tarski(k2_relat_1(B_203), A_204) | ~v1_funct_1(B_203) | ~v1_relat_1(B_203))), inference(cnfTransformation, [status(thm)], [f_118])).
% 17.62/8.38  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(A_2, B_3) | ~m1_subset_1(A_2, k1_zfmisc_1(B_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.62/8.38  tff(c_1025, plain, (![B_203, A_204]: (r1_tarski(B_203, k2_zfmisc_1(k1_relat_1(B_203), A_204)) | ~r1_tarski(k2_relat_1(B_203), A_204) | ~v1_funct_1(B_203) | ~v1_relat_1(B_203))), inference(resolution, [status(thm)], [c_987, c_4])).
% 17.62/8.38  tff(c_1282, plain, (![A_232, A_204]: (r1_tarski(k7_relat_1('#skF_4', A_232), k2_zfmisc_1(A_232, A_204)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_232)), A_204) | ~v1_funct_1(k7_relat_1('#skF_4', A_232)) | ~v1_relat_1(k7_relat_1('#skF_4', A_232)) | ~r1_tarski(A_232, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1276, c_1025])).
% 17.62/8.38  tff(c_1308, plain, (![A_232, A_204]: (r1_tarski(k7_relat_1('#skF_4', A_232), k2_zfmisc_1(A_232, A_204)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_232)), A_204) | ~v1_relat_1(k7_relat_1('#skF_4', A_232)) | ~r1_tarski(A_232, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_1282])).
% 17.62/8.38  tff(c_35903, plain, (![A_1208, A_1209]: (r1_tarski(k7_relat_1('#skF_4', A_1208), k2_zfmisc_1(A_1208, A_1209)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_1208)), A_1209) | ~r1_tarski(A_1208, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1612, c_1308])).
% 17.62/8.38  tff(c_35911, plain, (![A_1208, A_7]: (r1_tarski(k7_relat_1('#skF_4', A_1208), k2_zfmisc_1(A_1208, A_7)) | ~r1_tarski(A_1208, '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', A_1208), A_7) | ~v1_relat_1(k7_relat_1('#skF_4', A_1208)))), inference(resolution, [status(thm)], [c_12, c_35903])).
% 17.62/8.38  tff(c_35922, plain, (![A_1210, A_1211]: (r1_tarski(k7_relat_1('#skF_4', A_1210), k2_zfmisc_1(A_1210, A_1211)) | ~r1_tarski(A_1210, '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', A_1210), A_1211))), inference(demodulation, [status(thm), theory('equality')], [c_1612, c_35911])).
% 17.62/8.38  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.62/8.38  tff(c_514, plain, (![A_115, B_116, C_117, D_118]: (v1_funct_1(k2_partfun1(A_115, B_116, C_117, D_118)) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_1(C_117))), inference(cnfTransformation, [status(thm)], [f_100])).
% 17.62/8.38  tff(c_519, plain, (![D_118]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_118)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_514])).
% 17.62/8.38  tff(c_523, plain, (![D_118]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_118)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_519])).
% 17.62/8.38  tff(c_52, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 17.62/8.38  tff(c_70, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_52])).
% 17.62/8.38  tff(c_526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_523, c_70])).
% 17.62/8.38  tff(c_527, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_52])).
% 17.62/8.38  tff(c_645, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_527])).
% 17.62/8.38  tff(c_725, plain, (~r1_tarski(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_645])).
% 17.62/8.38  tff(c_1179, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1177, c_725])).
% 17.62/8.38  tff(c_35944, plain, (~r1_tarski('#skF_3', '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_35922, c_1179])).
% 17.62/8.38  tff(c_35996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1610, c_56, c_35944])).
% 17.62/8.38  tff(c_35998, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_527])).
% 17.62/8.38  tff(c_36290, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_35998, c_36279])).
% 17.62/8.38  tff(c_36599, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36594, c_36594, c_36290])).
% 17.62/8.38  tff(c_35997, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_527])).
% 17.62/8.38  tff(c_36606, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36594, c_35997])).
% 17.62/8.38  tff(c_36605, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36594, c_35998])).
% 17.62/8.38  tff(c_34, plain, (![B_25, C_26, A_24]: (k1_xboole_0=B_25 | v1_funct_2(C_26, A_24, B_25) | k1_relset_1(A_24, B_25, C_26)!=A_24 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.62/8.38  tff(c_36693, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_36605, c_34])).
% 17.62/8.38  tff(c_36718, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_36606, c_64, c_36693])).
% 17.62/8.38  tff(c_36737, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36599, c_36718])).
% 17.62/8.38  tff(c_36832, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_36823, c_36737])).
% 17.62/8.38  tff(c_36862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_36832])).
% 17.62/8.38  tff(c_36863, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_54])).
% 17.62/8.38  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.62/8.38  tff(c_36865, plain, (![A_1]: (r1_tarski('#skF_1', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_36863, c_2])).
% 17.62/8.38  tff(c_37375, plain, (![B_1367, A_1368]: (v1_relat_1(B_1367) | ~m1_subset_1(B_1367, k1_zfmisc_1(A_1368)) | ~v1_relat_1(A_1368))), inference(cnfTransformation, [status(thm)], [f_38])).
% 17.62/8.38  tff(c_37385, plain, (![A_1369, B_1370]: (v1_relat_1(A_1369) | ~v1_relat_1(B_1370) | ~r1_tarski(A_1369, B_1370))), inference(resolution, [status(thm)], [c_6, c_37375])).
% 17.62/8.38  tff(c_37400, plain, (![A_1]: (v1_relat_1('#skF_1') | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_36865, c_37385])).
% 17.62/8.38  tff(c_37402, plain, (![A_1]: (~v1_relat_1(A_1))), inference(splitLeft, [status(thm)], [c_37400])).
% 17.62/8.38  tff(c_37407, plain, (![C_17, A_15, B_16]: (~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(negUnitSimplification, [status(thm)], [c_37402, c_20])).
% 17.62/8.38  tff(c_36864, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_54])).
% 17.62/8.38  tff(c_36870, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36863, c_36864])).
% 17.62/8.38  tff(c_36877, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36870, c_58])).
% 17.62/8.38  tff(c_37409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37407, c_36877])).
% 17.62/8.38  tff(c_37410, plain, (v1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_37400])).
% 17.62/8.38  tff(c_38374, plain, (![C_1487, A_1488, B_1489]: (v4_relat_1(C_1487, A_1488) | ~m1_subset_1(C_1487, k1_zfmisc_1(k2_zfmisc_1(A_1488, B_1489))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 17.62/8.38  tff(c_38410, plain, (![A_1490, A_1491, B_1492]: (v4_relat_1(A_1490, A_1491) | ~r1_tarski(A_1490, k2_zfmisc_1(A_1491, B_1492)))), inference(resolution, [status(thm)], [c_6, c_38374])).
% 17.62/8.38  tff(c_38426, plain, (![A_1493]: (v4_relat_1('#skF_1', A_1493))), inference(resolution, [status(thm)], [c_36865, c_38410])).
% 17.62/8.38  tff(c_14, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.62/8.38  tff(c_38429, plain, (![A_1493]: (k7_relat_1('#skF_1', A_1493)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_38426, c_14])).
% 17.62/8.38  tff(c_38432, plain, (![A_1493]: (k7_relat_1('#skF_1', A_1493)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37410, c_38429])).
% 17.62/8.38  tff(c_38528, plain, (![B_1506, A_1507]: (k1_relat_1(k7_relat_1(B_1506, A_1507))=A_1507 | ~r1_tarski(A_1507, k1_relat_1(B_1506)) | ~v1_relat_1(B_1506))), inference(cnfTransformation, [status(thm)], [f_60])).
% 17.62/8.38  tff(c_38544, plain, (![B_1508]: (k1_relat_1(k7_relat_1(B_1508, '#skF_1'))='#skF_1' | ~v1_relat_1(B_1508))), inference(resolution, [status(thm)], [c_36865, c_38528])).
% 17.62/8.38  tff(c_38557, plain, (k1_relat_1('#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38432, c_38544])).
% 17.62/8.38  tff(c_38564, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_37410, c_38557])).
% 17.62/8.38  tff(c_38579, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_1', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38564, c_18])).
% 17.62/8.38  tff(c_38605, plain, (![A_1509]: (A_1509='#skF_1' | ~r1_tarski(A_1509, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_37410, c_38564, c_38432, c_38579])).
% 17.62/8.38  tff(c_38627, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_56, c_38605])).
% 17.62/8.38  tff(c_37415, plain, (![C_1374, A_1375, B_1376]: (v1_relat_1(C_1374) | ~m1_subset_1(C_1374, k1_zfmisc_1(k2_zfmisc_1(A_1375, B_1376))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 17.62/8.38  tff(c_37424, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36877, c_37415])).
% 17.62/8.38  tff(c_37443, plain, (![C_1382, B_1383, A_1384]: (v5_relat_1(C_1382, B_1383) | ~m1_subset_1(C_1382, k1_zfmisc_1(k2_zfmisc_1(A_1384, B_1383))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 17.62/8.38  tff(c_37452, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_36877, c_37443])).
% 17.62/8.38  tff(c_37453, plain, (![C_1385, A_1386, B_1387]: (v4_relat_1(C_1385, A_1386) | ~m1_subset_1(C_1385, k1_zfmisc_1(k2_zfmisc_1(A_1386, B_1387))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 17.62/8.38  tff(c_37463, plain, (![A_1388, A_1389, B_1390]: (v4_relat_1(A_1388, A_1389) | ~r1_tarski(A_1388, k2_zfmisc_1(A_1389, B_1390)))), inference(resolution, [status(thm)], [c_6, c_37453])).
% 17.62/8.38  tff(c_37478, plain, (![A_1389]: (v4_relat_1('#skF_1', A_1389))), inference(resolution, [status(thm)], [c_36865, c_37463])).
% 17.62/8.38  tff(c_37501, plain, (![B_1396, A_1397]: (k7_relat_1(B_1396, A_1397)=B_1396 | ~v4_relat_1(B_1396, A_1397) | ~v1_relat_1(B_1396))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.62/8.38  tff(c_37504, plain, (![A_1389]: (k7_relat_1('#skF_1', A_1389)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_37478, c_37501])).
% 17.62/8.38  tff(c_37510, plain, (![A_1389]: (k7_relat_1('#skF_1', A_1389)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37410, c_37504])).
% 17.62/8.38  tff(c_37575, plain, (![B_1401, A_1402]: (k1_relat_1(k7_relat_1(B_1401, A_1402))=A_1402 | ~r1_tarski(A_1402, k1_relat_1(B_1401)) | ~v1_relat_1(B_1401))), inference(cnfTransformation, [status(thm)], [f_60])).
% 17.62/8.38  tff(c_37591, plain, (![B_1403]: (k1_relat_1(k7_relat_1(B_1403, '#skF_1'))='#skF_1' | ~v1_relat_1(B_1403))), inference(resolution, [status(thm)], [c_36865, c_37575])).
% 17.62/8.38  tff(c_37604, plain, (k1_relat_1('#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_37510, c_37591])).
% 17.62/8.38  tff(c_37611, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_37410, c_37604])).
% 17.62/8.38  tff(c_37626, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_1', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_37611, c_18])).
% 17.62/8.38  tff(c_37632, plain, (![A_1404]: (A_1404='#skF_1' | ~r1_tarski(A_1404, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_37410, c_37611, c_37510, c_37626])).
% 17.62/8.38  tff(c_37710, plain, (![B_1408]: (k2_relat_1(B_1408)='#skF_1' | ~v5_relat_1(B_1408, '#skF_1') | ~v1_relat_1(B_1408))), inference(resolution, [status(thm)], [c_12, c_37632])).
% 17.62/8.38  tff(c_37717, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_37452, c_37710])).
% 17.62/8.38  tff(c_37723, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_37424, c_37717])).
% 17.62/8.38  tff(c_37462, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_36877, c_37453])).
% 17.62/8.38  tff(c_37507, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_37462, c_37501])).
% 17.62/8.38  tff(c_37513, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_37424, c_37507])).
% 17.62/8.38  tff(c_37607, plain, (k1_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_37513, c_37591])).
% 17.62/8.38  tff(c_37613, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_37424, c_37607])).
% 17.62/8.38  tff(c_38099, plain, (![B_1466, A_1467]: (m1_subset_1(B_1466, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1466), A_1467))) | ~r1_tarski(k2_relat_1(B_1466), A_1467) | ~v1_funct_1(B_1466) | ~v1_relat_1(B_1466))), inference(cnfTransformation, [status(thm)], [f_118])).
% 17.62/8.38  tff(c_38135, plain, (![A_1467]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_1467))) | ~r1_tarski(k2_relat_1('#skF_4'), A_1467) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_37613, c_38099])).
% 17.62/8.38  tff(c_38152, plain, (![A_1468]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_1468))))), inference(demodulation, [status(thm), theory('equality')], [c_37424, c_62, c_36865, c_37723, c_38135])).
% 17.62/8.38  tff(c_38205, plain, (![A_1468]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', A_1468)))), inference(resolution, [status(thm)], [c_38152, c_4])).
% 17.62/8.38  tff(c_38150, plain, (![A_1467]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_1467))))), inference(demodulation, [status(thm), theory('equality')], [c_37424, c_62, c_36865, c_37723, c_38135])).
% 17.62/8.38  tff(c_38206, plain, (![A_1469, B_1470, C_1471, D_1472]: (k2_partfun1(A_1469, B_1470, C_1471, D_1472)=k7_relat_1(C_1471, D_1472) | ~m1_subset_1(C_1471, k1_zfmisc_1(k2_zfmisc_1(A_1469, B_1470))) | ~v1_funct_1(C_1471))), inference(cnfTransformation, [status(thm)], [f_106])).
% 17.62/8.38  tff(c_38208, plain, (![A_1467, D_1472]: (k2_partfun1('#skF_1', A_1467, '#skF_4', D_1472)=k7_relat_1('#skF_4', D_1472) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_38150, c_38206])).
% 17.62/8.38  tff(c_38216, plain, (![A_1467, D_1472]: (k2_partfun1('#skF_1', A_1467, '#skF_4', D_1472)=k7_relat_1('#skF_4', D_1472))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_38208])).
% 17.62/8.38  tff(c_37654, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_56, c_37632])).
% 17.62/8.38  tff(c_37360, plain, (![A_1363, B_1364, C_1365, D_1366]: (v1_funct_1(k2_partfun1(A_1363, B_1364, C_1365, D_1366)) | ~m1_subset_1(C_1365, k1_zfmisc_1(k2_zfmisc_1(A_1363, B_1364))) | ~v1_funct_1(C_1365))), inference(cnfTransformation, [status(thm)], [f_100])).
% 17.62/8.38  tff(c_37365, plain, (![D_1366]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', D_1366)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_36877, c_37360])).
% 17.62/8.38  tff(c_37369, plain, (![D_1366]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', D_1366)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_37365])).
% 17.62/8.38  tff(c_36891, plain, (![B_1305, A_1306]: (v1_relat_1(B_1305) | ~m1_subset_1(B_1305, k1_zfmisc_1(A_1306)) | ~v1_relat_1(A_1306))), inference(cnfTransformation, [status(thm)], [f_38])).
% 17.62/8.38  tff(c_36901, plain, (![A_1307, B_1308]: (v1_relat_1(A_1307) | ~v1_relat_1(B_1308) | ~r1_tarski(A_1307, B_1308))), inference(resolution, [status(thm)], [c_6, c_36891])).
% 17.62/8.38  tff(c_36916, plain, (![A_1]: (v1_relat_1('#skF_1') | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_36865, c_36901])).
% 17.62/8.38  tff(c_36928, plain, (![A_1]: (~v1_relat_1(A_1))), inference(splitLeft, [status(thm)], [c_36916])).
% 17.62/8.38  tff(c_36918, plain, (![C_1309, A_1310, B_1311]: (v1_relat_1(C_1309) | ~m1_subset_1(C_1309, k1_zfmisc_1(k2_zfmisc_1(A_1310, B_1311))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 17.62/8.38  tff(c_36927, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36877, c_36918])).
% 17.62/8.38  tff(c_36933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36928, c_36927])).
% 17.62/8.38  tff(c_36934, plain, (v1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_36916])).
% 17.62/8.38  tff(c_37007, plain, (![C_1330, A_1331, B_1332]: (v4_relat_1(C_1330, A_1331) | ~m1_subset_1(C_1330, k1_zfmisc_1(k2_zfmisc_1(A_1331, B_1332))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 17.62/8.38  tff(c_37094, plain, (![A_1338, A_1339, B_1340]: (v4_relat_1(A_1338, A_1339) | ~r1_tarski(A_1338, k2_zfmisc_1(A_1339, B_1340)))), inference(resolution, [status(thm)], [c_6, c_37007])).
% 17.62/8.38  tff(c_37115, plain, (![A_1341]: (v4_relat_1('#skF_1', A_1341))), inference(resolution, [status(thm)], [c_36865, c_37094])).
% 17.62/8.38  tff(c_37118, plain, (![A_1341]: (k7_relat_1('#skF_1', A_1341)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_37115, c_14])).
% 17.62/8.38  tff(c_37133, plain, (![A_1345]: (k7_relat_1('#skF_1', A_1345)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36934, c_37118])).
% 17.62/8.38  tff(c_37017, plain, (![B_1333, A_1334]: (k1_relat_1(k7_relat_1(B_1333, A_1334))=A_1334 | ~r1_tarski(A_1334, k1_relat_1(B_1333)) | ~v1_relat_1(B_1333))), inference(cnfTransformation, [status(thm)], [f_60])).
% 17.62/8.38  tff(c_37032, plain, (![B_1333]: (k1_relat_1(k7_relat_1(B_1333, '#skF_1'))='#skF_1' | ~v1_relat_1(B_1333))), inference(resolution, [status(thm)], [c_36865, c_37017])).
% 17.62/8.38  tff(c_37139, plain, (k1_relat_1('#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_37133, c_37032])).
% 17.62/8.38  tff(c_37150, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36934, c_37139])).
% 17.62/8.38  tff(c_37121, plain, (![A_1341]: (k7_relat_1('#skF_1', A_1341)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36934, c_37118])).
% 17.62/8.38  tff(c_37159, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_1', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_37150, c_18])).
% 17.62/8.38  tff(c_37200, plain, (![A_1347]: (A_1347='#skF_1' | ~r1_tarski(A_1347, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36934, c_37150, c_37121, c_37159])).
% 17.62/8.38  tff(c_37222, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_56, c_37200])).
% 17.62/8.38  tff(c_36889, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36870, c_36870, c_36870, c_36870, c_36870, c_52])).
% 17.62/8.38  tff(c_36890, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_36889])).
% 17.62/8.38  tff(c_37224, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_37222, c_36890])).
% 17.62/8.38  tff(c_37372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37369, c_37224])).
% 17.62/8.38  tff(c_37373, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitRight, [status(thm)], [c_36889])).
% 17.62/8.38  tff(c_37414, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitLeft, [status(thm)], [c_37373])).
% 17.62/8.38  tff(c_37482, plain, (~r1_tarski(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_37414])).
% 17.62/8.38  tff(c_37655, plain, (~r1_tarski(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_37654, c_37654, c_37482])).
% 17.62/8.38  tff(c_38339, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38216, c_37655])).
% 17.62/8.38  tff(c_38343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38205, c_37513, c_38339])).
% 17.62/8.38  tff(c_38345, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitRight, [status(thm)], [c_37373])).
% 17.62/8.38  tff(c_38497, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_38345, c_20])).
% 17.62/8.38  tff(c_38631, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38627, c_38497])).
% 17.62/8.38  tff(c_39018, plain, (![A_1544, B_1545, C_1546, D_1547]: (v1_funct_1(k2_partfun1(A_1544, B_1545, C_1546, D_1547)) | ~m1_subset_1(C_1546, k1_zfmisc_1(k2_zfmisc_1(A_1544, B_1545))) | ~v1_funct_1(C_1546))), inference(cnfTransformation, [status(thm)], [f_100])).
% 17.62/8.38  tff(c_39025, plain, (![D_1547]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', D_1547)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_36877, c_39018])).
% 17.62/8.38  tff(c_39032, plain, (![D_1547]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', D_1547)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_39025])).
% 17.62/8.38  tff(c_38495, plain, (v5_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_38345, c_22])).
% 17.62/8.38  tff(c_38630, plain, (v5_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38627, c_38495])).
% 17.62/8.38  tff(c_38689, plain, (![B_1513]: (k2_relat_1(B_1513)='#skF_1' | ~v5_relat_1(B_1513, '#skF_1') | ~v1_relat_1(B_1513))), inference(resolution, [status(thm)], [c_12, c_38605])).
% 17.62/8.38  tff(c_38692, plain, (k2_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_38630, c_38689])).
% 17.62/8.38  tff(c_38702, plain, (k2_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38631, c_38692])).
% 17.62/8.38  tff(c_24, plain, (![C_20, A_18, B_19]: (v4_relat_1(C_20, A_18) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 17.62/8.38  tff(c_38496, plain, (v4_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_38345, c_24])).
% 17.62/8.38  tff(c_38502, plain, (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3')=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_38496, c_14])).
% 17.62/8.38  tff(c_38505, plain, (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3')=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38497, c_38502])).
% 17.62/8.38  tff(c_38998, plain, (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1')=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38627, c_38627, c_38627, c_38505])).
% 17.62/8.38  tff(c_38543, plain, (![B_1506]: (k1_relat_1(k7_relat_1(B_1506, '#skF_1'))='#skF_1' | ~v1_relat_1(B_1506))), inference(resolution, [status(thm)], [c_36865, c_38528])).
% 17.62/8.38  tff(c_39002, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38998, c_38543])).
% 17.62/8.38  tff(c_39012, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38631, c_39002])).
% 17.62/8.38  tff(c_48, plain, (![B_36, A_35]: (v1_funct_2(B_36, k1_relat_1(B_36), A_35) | ~r1_tarski(k2_relat_1(B_36), A_35) | ~v1_funct_1(B_36) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_118])).
% 17.62/8.38  tff(c_39039, plain, (![A_35]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', A_35) | ~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')), A_35) | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')) | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_39012, c_48])).
% 17.62/8.38  tff(c_39046, plain, (![A_35]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', A_35))), inference(demodulation, [status(thm), theory('equality')], [c_38631, c_39032, c_36865, c_38702, c_39039])).
% 17.62/8.38  tff(c_38344, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_37373])).
% 17.62/8.38  tff(c_38633, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38627, c_38627, c_38344])).
% 17.62/8.38  tff(c_39052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39046, c_38633])).
% 17.62/8.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.62/8.38  
% 17.62/8.38  Inference rules
% 17.62/8.38  ----------------------
% 17.62/8.38  #Ref     : 0
% 17.62/8.38  #Sup     : 8220
% 17.62/8.38  #Fact    : 0
% 17.62/8.38  #Define  : 0
% 17.62/8.38  #Split   : 49
% 17.62/8.38  #Chain   : 0
% 17.62/8.38  #Close   : 0
% 17.62/8.38  
% 17.62/8.38  Ordering : KBO
% 17.62/8.38  
% 17.62/8.38  Simplification rules
% 17.62/8.38  ----------------------
% 17.62/8.38  #Subsume      : 2537
% 17.62/8.38  #Demod        : 13369
% 17.62/8.38  #Tautology    : 2874
% 17.62/8.38  #SimpNegUnit  : 371
% 17.62/8.38  #BackRed      : 86
% 17.62/8.38  
% 17.62/8.38  #Partial instantiations: 0
% 17.62/8.38  #Strategies tried      : 1
% 17.62/8.38  
% 17.62/8.38  Timing (in seconds)
% 17.62/8.38  ----------------------
% 17.62/8.39  Preprocessing        : 0.35
% 17.62/8.39  Parsing              : 0.19
% 17.62/8.39  CNF conversion       : 0.02
% 17.62/8.39  Main loop            : 7.22
% 17.62/8.39  Inferencing          : 1.58
% 17.62/8.39  Reduction            : 3.44
% 17.62/8.39  Demodulation         : 2.82
% 17.62/8.39  BG Simplification    : 0.12
% 17.62/8.39  Subsumption          : 1.73
% 17.62/8.39  Abstraction          : 0.23
% 17.62/8.39  MUC search           : 0.00
% 17.62/8.39  Cooper               : 0.00
% 17.62/8.39  Total                : 7.64
% 17.62/8.39  Index Insertion      : 0.00
% 17.62/8.39  Index Deletion       : 0.00
% 17.62/8.39  Index Matching       : 0.00
% 17.62/8.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
