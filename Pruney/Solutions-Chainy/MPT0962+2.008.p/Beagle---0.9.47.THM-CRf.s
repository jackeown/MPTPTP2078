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
% DateTime   : Thu Dec  3 10:10:52 EST 2020

% Result     : Theorem 23.94s
% Output     : CNFRefutation 23.94s
% Verified   : 
% Statistics : Number of formulae       :  180 (1011 expanded)
%              Number of leaves         :   33 ( 346 expanded)
%              Depth                    :   22
%              Number of atoms          :  334 (2162 expanded)
%              Number of equality atoms :   62 ( 447 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
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

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(c_56,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_60,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_20,plain,(
    ! [C_13,A_11,B_12] :
      ( r1_tarski(k2_zfmisc_1(C_13,A_11),k2_zfmisc_1(C_13,B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_70163,plain,(
    ! [A_1244] :
      ( r1_tarski(A_1244,k2_zfmisc_1(k1_relat_1(A_1244),k2_relat_1(A_1244)))
      | ~ v1_relat_1(A_1244) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_76866,plain,(
    ! [A_1542] :
      ( k2_xboole_0(A_1542,k2_zfmisc_1(k1_relat_1(A_1542),k2_relat_1(A_1542))) = k2_zfmisc_1(k1_relat_1(A_1542),k2_relat_1(A_1542))
      | ~ v1_relat_1(A_1542) ) ),
    inference(resolution,[status(thm)],[c_70163,c_10])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_82463,plain,(
    ! [A_1690,C_1691] :
      ( r1_tarski(A_1690,C_1691)
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_1690),k2_relat_1(A_1690)),C_1691)
      | ~ v1_relat_1(A_1690) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76866,c_8])).

tff(c_105158,plain,(
    ! [A_2044,B_2045] :
      ( r1_tarski(A_2044,k2_zfmisc_1(k1_relat_1(A_2044),B_2045))
      | ~ v1_relat_1(A_2044)
      | ~ r1_tarski(k2_relat_1(A_2044),B_2045) ) ),
    inference(resolution,[status(thm)],[c_20,c_82463])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,(
    ! [A_35,B_36] :
      ( k2_xboole_0(A_35,B_36) = B_36
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_102,plain,(
    k2_xboole_0(k2_relat_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_56,c_92])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_232,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_tarski(A_58,C_59)
      | ~ r1_tarski(k2_xboole_0(A_58,B_60),C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_247,plain,(
    ! [A_58,B_60] : r1_tarski(A_58,k2_xboole_0(A_58,B_60)) ),
    inference(resolution,[status(thm)],[c_6,c_232])).

tff(c_1063,plain,(
    ! [C_136,A_137,B_138] :
      ( r1_tarski(k2_zfmisc_1(C_136,A_137),k2_zfmisc_1(C_136,B_138))
      | ~ r1_tarski(A_137,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5474,plain,(
    ! [C_316,A_317,B_318] :
      ( k2_xboole_0(k2_zfmisc_1(C_316,A_317),k2_zfmisc_1(C_316,B_318)) = k2_zfmisc_1(C_316,B_318)
      | ~ r1_tarski(A_317,B_318) ) ),
    inference(resolution,[status(thm)],[c_1063,c_10])).

tff(c_20010,plain,(
    ! [C_673,A_674,C_675,B_676] :
      ( r1_tarski(k2_zfmisc_1(C_673,A_674),C_675)
      | ~ r1_tarski(k2_zfmisc_1(C_673,B_676),C_675)
      | ~ r1_tarski(A_674,B_676) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5474,c_8])).

tff(c_63021,plain,(
    ! [C_1160,A_1161,B_1162,A_1163] :
      ( r1_tarski(k2_zfmisc_1(C_1160,A_1161),k2_zfmisc_1(C_1160,B_1162))
      | ~ r1_tarski(A_1161,A_1163)
      | ~ r1_tarski(A_1163,B_1162) ) ),
    inference(resolution,[status(thm)],[c_20,c_20010])).

tff(c_64601,plain,(
    ! [C_1185,A_1186,B_1187,B_1188] :
      ( r1_tarski(k2_zfmisc_1(C_1185,A_1186),k2_zfmisc_1(C_1185,B_1187))
      | ~ r1_tarski(k2_xboole_0(A_1186,B_1188),B_1187) ) ),
    inference(resolution,[status(thm)],[c_247,c_63021])).

tff(c_64793,plain,(
    ! [C_1192,A_1193,B_1194] : r1_tarski(k2_zfmisc_1(C_1192,A_1193),k2_zfmisc_1(C_1192,k2_xboole_0(A_1193,B_1194))) ),
    inference(resolution,[status(thm)],[c_6,c_64601])).

tff(c_65457,plain,(
    ! [C_1199] : r1_tarski(k2_zfmisc_1(C_1199,k2_relat_1('#skF_2')),k2_zfmisc_1(C_1199,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_64793])).

tff(c_435,plain,(
    ! [A_84] :
      ( r1_tarski(A_84,k2_zfmisc_1(k1_relat_1(A_84),k2_relat_1(A_84)))
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6705,plain,(
    ! [A_358] :
      ( k2_xboole_0(A_358,k2_zfmisc_1(k1_relat_1(A_358),k2_relat_1(A_358))) = k2_zfmisc_1(k1_relat_1(A_358),k2_relat_1(A_358))
      | ~ v1_relat_1(A_358) ) ),
    inference(resolution,[status(thm)],[c_435,c_10])).

tff(c_6831,plain,(
    ! [A_358,C_5] :
      ( r1_tarski(A_358,C_5)
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_358),k2_relat_1(A_358)),C_5)
      | ~ v1_relat_1(A_358) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6705,c_8])).

tff(c_65501,plain,
    ( r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_65457,c_6831])).

tff(c_65686,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_65501])).

tff(c_1567,plain,(
    ! [A_172,B_173,C_174] :
      ( k1_relset_1(A_172,B_173,C_174) = k1_relat_1(C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1578,plain,(
    ! [A_172,B_173,A_14] :
      ( k1_relset_1(A_172,B_173,A_14) = k1_relat_1(A_14)
      | ~ r1_tarski(A_14,k2_zfmisc_1(A_172,B_173)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1567])).

tff(c_65833,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_65686,c_1578])).

tff(c_58,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54])).

tff(c_296,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_3585,plain,(
    ! [B_255,C_256,A_257] :
      ( k1_xboole_0 = B_255
      | v1_funct_2(C_256,A_257,B_255)
      | k1_relset_1(A_257,B_255,C_256) != A_257
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_257,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_3614,plain,(
    ! [B_255,A_14,A_257] :
      ( k1_xboole_0 = B_255
      | v1_funct_2(A_14,A_257,B_255)
      | k1_relset_1(A_257,B_255,A_14) != A_257
      | ~ r1_tarski(A_14,k2_zfmisc_1(A_257,B_255)) ) ),
    inference(resolution,[status(thm)],[c_26,c_3585])).

tff(c_65771,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_65686,c_3614])).

tff(c_65827,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_296,c_65771])).

tff(c_66863,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65833,c_65827])).

tff(c_12,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_104,plain,(
    ! [A_8] : k2_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_12,c_92])).

tff(c_16,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1101,plain,(
    ! [A_139,A_140] :
      ( r1_tarski(k2_zfmisc_1(A_139,A_140),k1_xboole_0)
      | ~ r1_tarski(A_140,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1063])).

tff(c_1281,plain,(
    ! [A_155,A_156] :
      ( k2_xboole_0(k2_zfmisc_1(A_155,A_156),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_156,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1101,c_10])).

tff(c_248,plain,(
    ! [A_61,B_62] : r1_tarski(A_61,k2_xboole_0(A_61,B_62)) ),
    inference(resolution,[status(thm)],[c_6,c_232])).

tff(c_267,plain,(
    ! [A_3,B_4,B_62] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_62)) ),
    inference(resolution,[status(thm)],[c_248,c_8])).

tff(c_1293,plain,(
    ! [A_155,A_156,B_62] :
      ( r1_tarski(k2_zfmisc_1(A_155,A_156),k2_xboole_0(k1_xboole_0,B_62))
      | ~ r1_tarski(A_156,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1281,c_267])).

tff(c_1311,plain,(
    ! [A_155,A_156,B_62] :
      ( r1_tarski(k2_zfmisc_1(A_155,A_156),B_62)
      | ~ r1_tarski(A_156,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1293])).

tff(c_876,plain,(
    ! [A_120,C_121,B_122] :
      ( r1_tarski(k2_zfmisc_1(A_120,C_121),k2_zfmisc_1(B_122,C_121))
      | ~ r1_tarski(A_120,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10710,plain,(
    ! [B_464,C_465,A_466] :
      ( k2_zfmisc_1(B_464,C_465) = k2_zfmisc_1(A_466,C_465)
      | ~ r1_tarski(k2_zfmisc_1(B_464,C_465),k2_zfmisc_1(A_466,C_465))
      | ~ r1_tarski(A_466,B_464) ) ),
    inference(resolution,[status(thm)],[c_876,c_2])).

tff(c_39333,plain,(
    ! [A_955,A_954,A_953] :
      ( k2_zfmisc_1(A_955,A_954) = k2_zfmisc_1(A_953,A_954)
      | ~ r1_tarski(A_953,A_955)
      | ~ r1_tarski(A_954,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1311,c_10710])).

tff(c_39517,plain,(
    ! [A_954] :
      ( k2_zfmisc_1(k2_relat_1('#skF_2'),A_954) = k2_zfmisc_1('#skF_1',A_954)
      | ~ r1_tarski(A_954,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_56,c_39333])).

tff(c_18,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_914,plain,(
    ! [A_123,B_124] :
      ( r1_tarski(k2_zfmisc_1(A_123,B_124),k1_xboole_0)
      | ~ r1_tarski(A_123,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_876])).

tff(c_1453,plain,(
    ! [A_167,B_168] :
      ( k2_xboole_0(k2_zfmisc_1(A_167,B_168),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_167,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_914,c_10])).

tff(c_1471,plain,(
    ! [A_167,B_168,B_62] :
      ( r1_tarski(k2_zfmisc_1(A_167,B_168),k2_xboole_0(k1_xboole_0,B_62))
      | ~ r1_tarski(A_167,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1453,c_267])).

tff(c_1503,plain,(
    ! [A_169,B_170,B_171] :
      ( r1_tarski(k2_zfmisc_1(A_169,B_170),B_171)
      | ~ r1_tarski(A_169,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1471])).

tff(c_1563,plain,(
    ! [A_169,B_170,B_171] :
      ( k2_xboole_0(k2_zfmisc_1(A_169,B_170),B_171) = B_171
      | ~ r1_tarski(A_169,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1503,c_10])).

tff(c_551,plain,(
    ! [B_92,A_93] :
      ( r1_tarski(k1_relat_1(B_92),A_93)
      | ~ v4_relat_1(B_92,A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2621,plain,(
    ! [B_215,A_216] :
      ( k2_xboole_0(k1_relat_1(B_215),A_216) = A_216
      | ~ v4_relat_1(B_215,A_216)
      | ~ v1_relat_1(B_215) ) ),
    inference(resolution,[status(thm)],[c_551,c_10])).

tff(c_8466,plain,(
    ! [B_413,A_414,B_415] :
      ( r1_tarski(k1_relat_1(B_413),k2_xboole_0(A_414,B_415))
      | ~ v4_relat_1(B_413,A_414)
      | ~ v1_relat_1(B_413) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2621,c_267])).

tff(c_28,plain,(
    ! [B_17,A_16] :
      ( v4_relat_1(B_17,A_16)
      | ~ r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8544,plain,(
    ! [B_413,A_414,B_415] :
      ( v4_relat_1(B_413,k2_xboole_0(A_414,B_415))
      | ~ v4_relat_1(B_413,A_414)
      | ~ v1_relat_1(B_413) ) ),
    inference(resolution,[status(thm)],[c_8466,c_28])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1495,plain,(
    ! [A_167,B_168,B_62] :
      ( r1_tarski(k2_zfmisc_1(A_167,B_168),B_62)
      | ~ r1_tarski(A_167,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1471])).

tff(c_11528,plain,(
    ! [C_487,B_488,A_489] :
      ( k2_zfmisc_1(C_487,B_488) = k2_zfmisc_1(C_487,A_489)
      | ~ r1_tarski(k2_zfmisc_1(C_487,B_488),k2_zfmisc_1(C_487,A_489))
      | ~ r1_tarski(A_489,B_488) ) ),
    inference(resolution,[status(thm)],[c_1063,c_2])).

tff(c_43238,plain,(
    ! [A_975,B_976,A_977] :
      ( k2_zfmisc_1(A_975,B_976) = k2_zfmisc_1(A_975,A_977)
      | ~ r1_tarski(A_977,B_976)
      | ~ r1_tarski(A_975,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1495,c_11528])).

tff(c_43433,plain,(
    ! [A_978] :
      ( k2_zfmisc_1(A_978,k2_relat_1('#skF_2')) = k2_zfmisc_1(A_978,'#skF_1')
      | ~ r1_tarski(A_978,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_56,c_43238])).

tff(c_22,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_tarski(k2_zfmisc_1(A_11,C_13),k2_zfmisc_1(B_12,C_13))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14716,plain,(
    ! [A_574,C_575] :
      ( r1_tarski(A_574,C_575)
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_574),k2_relat_1(A_574)),C_575)
      | ~ v1_relat_1(A_574) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6705,c_8])).

tff(c_14818,plain,(
    ! [A_574,B_12] :
      ( r1_tarski(A_574,k2_zfmisc_1(B_12,k2_relat_1(A_574)))
      | ~ v1_relat_1(A_574)
      | ~ r1_tarski(k1_relat_1(A_574),B_12) ) ),
    inference(resolution,[status(thm)],[c_22,c_14716])).

tff(c_43473,plain,(
    ! [A_978] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_978,'#skF_1'))
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_978)
      | ~ r1_tarski(A_978,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43433,c_14818])).

tff(c_59685,plain,(
    ! [A_1121] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_1121,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_1121)
      | ~ r1_tarski(A_1121,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_43473])).

tff(c_59761,plain,(
    ! [A_16] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_16,'#skF_1'))
      | ~ r1_tarski(A_16,k1_xboole_0)
      | ~ v4_relat_1('#skF_2',A_16)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_59685])).

tff(c_59821,plain,(
    ! [A_1122] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_1122,'#skF_1'))
      | ~ r1_tarski(A_1122,k1_xboole_0)
      | ~ v4_relat_1('#skF_2',A_1122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_59761])).

tff(c_327,plain,(
    ! [C_67,B_68,A_69] :
      ( v5_relat_1(C_67,B_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_338,plain,(
    ! [A_14,B_68,A_69] :
      ( v5_relat_1(A_14,B_68)
      | ~ r1_tarski(A_14,k2_zfmisc_1(A_69,B_68)) ) ),
    inference(resolution,[status(thm)],[c_26,c_327])).

tff(c_44222,plain,(
    ! [A_14,A_978] :
      ( v5_relat_1(A_14,k2_relat_1('#skF_2'))
      | ~ r1_tarski(A_14,k2_zfmisc_1(A_978,'#skF_1'))
      | ~ r1_tarski(A_978,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43433,c_338])).

tff(c_59938,plain,(
    ! [A_1122] :
      ( v5_relat_1('#skF_2',k2_relat_1('#skF_2'))
      | ~ r1_tarski(A_1122,k1_xboole_0)
      | ~ v4_relat_1('#skF_2',A_1122) ) ),
    inference(resolution,[status(thm)],[c_59821,c_44222])).

tff(c_59984,plain,(
    ! [A_1123] :
      ( ~ r1_tarski(A_1123,k1_xboole_0)
      | ~ v4_relat_1('#skF_2',A_1123) ) ),
    inference(splitLeft,[status(thm)],[c_59938])).

tff(c_60008,plain,(
    ! [A_414,B_415] :
      ( ~ r1_tarski(k2_xboole_0(A_414,B_415),k1_xboole_0)
      | ~ v4_relat_1('#skF_2',A_414)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8544,c_59984])).

tff(c_60316,plain,(
    ! [A_1127,B_1128] :
      ( ~ r1_tarski(k2_xboole_0(A_1127,B_1128),k1_xboole_0)
      | ~ v4_relat_1('#skF_2',A_1127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60008])).

tff(c_60391,plain,(
    ! [B_171,A_169,B_170] :
      ( ~ r1_tarski(B_171,k1_xboole_0)
      | ~ v4_relat_1('#skF_2',k2_zfmisc_1(A_169,B_170))
      | ~ r1_tarski(A_169,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1563,c_60316])).

tff(c_61318,plain,(
    ! [A_1150,B_1151] :
      ( ~ v4_relat_1('#skF_2',k2_zfmisc_1(A_1150,B_1151))
      | ~ r1_tarski(A_1150,k1_xboole_0) ) ),
    inference(splitLeft,[status(thm)],[c_60391])).

tff(c_61348,plain,(
    ! [A_954] :
      ( ~ v4_relat_1('#skF_2',k2_zfmisc_1('#skF_1',A_954))
      | ~ r1_tarski(k2_relat_1('#skF_2'),k1_xboole_0)
      | ~ r1_tarski(A_954,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39517,c_61318])).

tff(c_61433,plain,(
    ~ r1_tarski(k2_relat_1('#skF_2'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_61348])).

tff(c_66867,plain,(
    ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66863,c_61433])).

tff(c_67117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_66867])).

tff(c_67119,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_61348])).

tff(c_1318,plain,(
    ! [A_157,A_158,B_159] :
      ( r1_tarski(k2_zfmisc_1(A_157,A_158),B_159)
      | ~ r1_tarski(A_158,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1293])).

tff(c_1378,plain,(
    ! [A_157,A_158,B_159] :
      ( k2_xboole_0(k2_zfmisc_1(A_157,A_158),B_159) = B_159
      | ~ r1_tarski(A_158,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1318,c_10])).

tff(c_11283,plain,(
    ! [A_479,B_480] :
      ( r1_tarski(A_479,k2_xboole_0(k2_zfmisc_1(k1_relat_1(A_479),k2_relat_1(A_479)),B_480))
      | ~ v1_relat_1(A_479) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6705,c_267])).

tff(c_11344,plain,(
    ! [A_479,B_159] :
      ( r1_tarski(A_479,B_159)
      | ~ v1_relat_1(A_479)
      | ~ r1_tarski(k2_relat_1(A_479),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1378,c_11283])).

tff(c_67236,plain,(
    ! [B_159] :
      ( r1_tarski('#skF_2',B_159)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_67119,c_11344])).

tff(c_67305,plain,(
    ! [B_159] : r1_tarski('#skF_2',B_159) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_67236])).

tff(c_689,plain,(
    ! [C_104,A_105,B_106] :
      ( v4_relat_1(C_104,A_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_701,plain,(
    ! [C_107,A_108] :
      ( v4_relat_1(C_107,A_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_689])).

tff(c_705,plain,(
    ! [A_14,A_108] :
      ( v4_relat_1(A_14,A_108)
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_701])).

tff(c_8535,plain,(
    ! [B_413,A_8] :
      ( r1_tarski(k1_relat_1(B_413),A_8)
      | ~ v4_relat_1(B_413,k1_xboole_0)
      | ~ v1_relat_1(B_413) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_8466])).

tff(c_32,plain,(
    ! [A_18] :
      ( r1_tarski(A_18,k2_zfmisc_1(k1_relat_1(A_18),k2_relat_1(A_18)))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_44216,plain,
    ( r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_43433,c_32])).

tff(c_44335,plain,
    ( r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_44216])).

tff(c_44346,plain,(
    ~ r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_44335])).

tff(c_44352,plain,
    ( ~ v4_relat_1('#skF_2',k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8535,c_44346])).

tff(c_44361,plain,(
    ~ v4_relat_1('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_44352])).

tff(c_44368,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_705,c_44361])).

tff(c_67326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67305,c_44368])).

tff(c_67328,plain,(
    r1_tarski(k1_relat_1('#skF_2'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_44335])).

tff(c_11348,plain,(
    ! [A_479,B_171] :
      ( r1_tarski(A_479,B_171)
      | ~ v1_relat_1(A_479)
      | ~ r1_tarski(k1_relat_1(A_479),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1563,c_11283])).

tff(c_68185,plain,(
    ! [B_171] :
      ( r1_tarski('#skF_2',B_171)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_67328,c_11348])).

tff(c_68264,plain,(
    ! [B_1217] : r1_tarski('#skF_2',B_1217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_68185])).

tff(c_143,plain,(
    ! [B_43,A_44] :
      ( B_43 = A_44
      | ~ r1_tarski(B_43,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_155,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_143])).

tff(c_68431,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_68264,c_155])).

tff(c_169,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_179,plain,(
    ! [C_49] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_169])).

tff(c_185,plain,(
    ! [A_50] :
      ( v1_relat_1(A_50)
      | ~ r1_tarski(A_50,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_179])).

tff(c_194,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_185])).

tff(c_42,plain,(
    ! [A_28] :
      ( v1_funct_2(k1_xboole_0,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_28,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_66,plain,(
    ! [A_28] :
      ( v1_funct_2(k1_xboole_0,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_42])).

tff(c_712,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_715,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_712])).

tff(c_719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_715])).

tff(c_721,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_696,plain,(
    ! [C_104,A_9] :
      ( v4_relat_1(C_104,A_9)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_689])).

tff(c_739,plain,(
    ! [A_111] : v4_relat_1(k1_xboole_0,A_111) ),
    inference(resolution,[status(thm)],[c_721,c_696])).

tff(c_576,plain,(
    ! [B_92] :
      ( k1_relat_1(B_92) = k1_xboole_0
      | ~ v4_relat_1(B_92,k1_xboole_0)
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_551,c_155])).

tff(c_743,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_739,c_576])).

tff(c_746,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_743])).

tff(c_2690,plain,(
    ! [B_217,C_218] :
      ( k1_relset_1(k1_xboole_0,B_217,C_218) = k1_relat_1(C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1567])).

tff(c_2692,plain,(
    ! [B_217] : k1_relset_1(k1_xboole_0,B_217,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_721,c_2690])).

tff(c_2697,plain,(
    ! [B_217] : k1_relset_1(k1_xboole_0,B_217,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_746,c_2692])).

tff(c_46,plain,(
    ! [C_30,B_29] :
      ( v1_funct_2(C_30,k1_xboole_0,B_29)
      | k1_relset_1(k1_xboole_0,B_29,C_30) != k1_xboole_0
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2423,plain,(
    ! [C_199,B_200] :
      ( v1_funct_2(C_199,k1_xboole_0,B_200)
      | k1_relset_1(k1_xboole_0,B_200,C_199) != k1_xboole_0
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_46])).

tff(c_2429,plain,(
    ! [B_200] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_200)
      | k1_relset_1(k1_xboole_0,B_200,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_721,c_2423])).

tff(c_2700,plain,(
    ! [B_200] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_200) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2697,c_2429])).

tff(c_68700,plain,(
    ! [B_200] : v1_funct_2('#skF_2','#skF_2',B_200) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68431,c_68431,c_2700])).

tff(c_68211,plain,
    ( k1_relat_1('#skF_2') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_67328,c_2])).

tff(c_68262,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_68211])).

tff(c_68752,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68431,c_68262])).

tff(c_68754,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68752,c_296])).

tff(c_69896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68700,c_68754])).

tff(c_69897,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_69902,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_69897])).

tff(c_105240,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_105158,c_69902])).

tff(c_105368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_105240])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:03:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.94/13.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.94/13.74  
% 23.94/13.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.94/13.74  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 23.94/13.74  
% 23.94/13.74  %Foreground sorts:
% 23.94/13.74  
% 23.94/13.74  
% 23.94/13.74  %Background operators:
% 23.94/13.74  
% 23.94/13.74  
% 23.94/13.74  %Foreground operators:
% 23.94/13.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 23.94/13.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.94/13.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.94/13.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.94/13.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 23.94/13.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 23.94/13.74  tff('#skF_2', type, '#skF_2': $i).
% 23.94/13.74  tff('#skF_1', type, '#skF_1': $i).
% 23.94/13.74  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 23.94/13.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 23.94/13.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.94/13.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.94/13.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 23.94/13.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 23.94/13.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.94/13.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 23.94/13.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 23.94/13.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 23.94/13.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.94/13.74  
% 23.94/13.77  tff(f_112, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 23.94/13.77  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 23.94/13.77  tff(f_67, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 23.94/13.77  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 23.94/13.77  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 23.94/13.77  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 23.94/13.77  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 23.94/13.77  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 23.94/13.77  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 23.94/13.77  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 23.94/13.77  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 23.94/13.77  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 23.94/13.77  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 23.94/13.77  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 23.94/13.77  tff(c_56, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 23.94/13.77  tff(c_60, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 23.94/13.77  tff(c_20, plain, (![C_13, A_11, B_12]: (r1_tarski(k2_zfmisc_1(C_13, A_11), k2_zfmisc_1(C_13, B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 23.94/13.77  tff(c_70163, plain, (![A_1244]: (r1_tarski(A_1244, k2_zfmisc_1(k1_relat_1(A_1244), k2_relat_1(A_1244))) | ~v1_relat_1(A_1244))), inference(cnfTransformation, [status(thm)], [f_67])).
% 23.94/13.77  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 23.94/13.77  tff(c_76866, plain, (![A_1542]: (k2_xboole_0(A_1542, k2_zfmisc_1(k1_relat_1(A_1542), k2_relat_1(A_1542)))=k2_zfmisc_1(k1_relat_1(A_1542), k2_relat_1(A_1542)) | ~v1_relat_1(A_1542))), inference(resolution, [status(thm)], [c_70163, c_10])).
% 23.94/13.77  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 23.94/13.77  tff(c_82463, plain, (![A_1690, C_1691]: (r1_tarski(A_1690, C_1691) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_1690), k2_relat_1(A_1690)), C_1691) | ~v1_relat_1(A_1690))), inference(superposition, [status(thm), theory('equality')], [c_76866, c_8])).
% 23.94/13.77  tff(c_105158, plain, (![A_2044, B_2045]: (r1_tarski(A_2044, k2_zfmisc_1(k1_relat_1(A_2044), B_2045)) | ~v1_relat_1(A_2044) | ~r1_tarski(k2_relat_1(A_2044), B_2045))), inference(resolution, [status(thm)], [c_20, c_82463])).
% 23.94/13.77  tff(c_26, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 23.94/13.77  tff(c_92, plain, (![A_35, B_36]: (k2_xboole_0(A_35, B_36)=B_36 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 23.94/13.77  tff(c_102, plain, (k2_xboole_0(k2_relat_1('#skF_2'), '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_56, c_92])).
% 23.94/13.77  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.94/13.77  tff(c_232, plain, (![A_58, C_59, B_60]: (r1_tarski(A_58, C_59) | ~r1_tarski(k2_xboole_0(A_58, B_60), C_59))), inference(cnfTransformation, [status(thm)], [f_35])).
% 23.94/13.77  tff(c_247, plain, (![A_58, B_60]: (r1_tarski(A_58, k2_xboole_0(A_58, B_60)))), inference(resolution, [status(thm)], [c_6, c_232])).
% 23.94/13.77  tff(c_1063, plain, (![C_136, A_137, B_138]: (r1_tarski(k2_zfmisc_1(C_136, A_137), k2_zfmisc_1(C_136, B_138)) | ~r1_tarski(A_137, B_138))), inference(cnfTransformation, [status(thm)], [f_53])).
% 23.94/13.77  tff(c_5474, plain, (![C_316, A_317, B_318]: (k2_xboole_0(k2_zfmisc_1(C_316, A_317), k2_zfmisc_1(C_316, B_318))=k2_zfmisc_1(C_316, B_318) | ~r1_tarski(A_317, B_318))), inference(resolution, [status(thm)], [c_1063, c_10])).
% 23.94/13.77  tff(c_20010, plain, (![C_673, A_674, C_675, B_676]: (r1_tarski(k2_zfmisc_1(C_673, A_674), C_675) | ~r1_tarski(k2_zfmisc_1(C_673, B_676), C_675) | ~r1_tarski(A_674, B_676))), inference(superposition, [status(thm), theory('equality')], [c_5474, c_8])).
% 23.94/13.77  tff(c_63021, plain, (![C_1160, A_1161, B_1162, A_1163]: (r1_tarski(k2_zfmisc_1(C_1160, A_1161), k2_zfmisc_1(C_1160, B_1162)) | ~r1_tarski(A_1161, A_1163) | ~r1_tarski(A_1163, B_1162))), inference(resolution, [status(thm)], [c_20, c_20010])).
% 23.94/13.77  tff(c_64601, plain, (![C_1185, A_1186, B_1187, B_1188]: (r1_tarski(k2_zfmisc_1(C_1185, A_1186), k2_zfmisc_1(C_1185, B_1187)) | ~r1_tarski(k2_xboole_0(A_1186, B_1188), B_1187))), inference(resolution, [status(thm)], [c_247, c_63021])).
% 23.94/13.77  tff(c_64793, plain, (![C_1192, A_1193, B_1194]: (r1_tarski(k2_zfmisc_1(C_1192, A_1193), k2_zfmisc_1(C_1192, k2_xboole_0(A_1193, B_1194))))), inference(resolution, [status(thm)], [c_6, c_64601])).
% 23.94/13.77  tff(c_65457, plain, (![C_1199]: (r1_tarski(k2_zfmisc_1(C_1199, k2_relat_1('#skF_2')), k2_zfmisc_1(C_1199, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_102, c_64793])).
% 23.94/13.77  tff(c_435, plain, (![A_84]: (r1_tarski(A_84, k2_zfmisc_1(k1_relat_1(A_84), k2_relat_1(A_84))) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_67])).
% 23.94/13.77  tff(c_6705, plain, (![A_358]: (k2_xboole_0(A_358, k2_zfmisc_1(k1_relat_1(A_358), k2_relat_1(A_358)))=k2_zfmisc_1(k1_relat_1(A_358), k2_relat_1(A_358)) | ~v1_relat_1(A_358))), inference(resolution, [status(thm)], [c_435, c_10])).
% 23.94/13.77  tff(c_6831, plain, (![A_358, C_5]: (r1_tarski(A_358, C_5) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_358), k2_relat_1(A_358)), C_5) | ~v1_relat_1(A_358))), inference(superposition, [status(thm), theory('equality')], [c_6705, c_8])).
% 23.94/13.77  tff(c_65501, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_65457, c_6831])).
% 23.94/13.77  tff(c_65686, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_65501])).
% 23.94/13.77  tff(c_1567, plain, (![A_172, B_173, C_174]: (k1_relset_1(A_172, B_173, C_174)=k1_relat_1(C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 23.94/13.77  tff(c_1578, plain, (![A_172, B_173, A_14]: (k1_relset_1(A_172, B_173, A_14)=k1_relat_1(A_14) | ~r1_tarski(A_14, k2_zfmisc_1(A_172, B_173)))), inference(resolution, [status(thm)], [c_26, c_1567])).
% 23.94/13.77  tff(c_65833, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_65686, c_1578])).
% 23.94/13.77  tff(c_58, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 23.94/13.77  tff(c_54, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 23.94/13.77  tff(c_62, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54])).
% 23.94/13.77  tff(c_296, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_62])).
% 23.94/13.77  tff(c_3585, plain, (![B_255, C_256, A_257]: (k1_xboole_0=B_255 | v1_funct_2(C_256, A_257, B_255) | k1_relset_1(A_257, B_255, C_256)!=A_257 | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_257, B_255))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 23.94/13.77  tff(c_3614, plain, (![B_255, A_14, A_257]: (k1_xboole_0=B_255 | v1_funct_2(A_14, A_257, B_255) | k1_relset_1(A_257, B_255, A_14)!=A_257 | ~r1_tarski(A_14, k2_zfmisc_1(A_257, B_255)))), inference(resolution, [status(thm)], [c_26, c_3585])).
% 23.94/13.77  tff(c_65771, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_65686, c_3614])).
% 23.94/13.77  tff(c_65827, plain, (k1_xboole_0='#skF_1' | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_296, c_65771])).
% 23.94/13.77  tff(c_66863, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_65833, c_65827])).
% 23.94/13.77  tff(c_12, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.94/13.77  tff(c_104, plain, (![A_8]: (k2_xboole_0(k1_xboole_0, A_8)=A_8)), inference(resolution, [status(thm)], [c_12, c_92])).
% 23.94/13.77  tff(c_16, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 23.94/13.77  tff(c_1101, plain, (![A_139, A_140]: (r1_tarski(k2_zfmisc_1(A_139, A_140), k1_xboole_0) | ~r1_tarski(A_140, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1063])).
% 23.94/13.77  tff(c_1281, plain, (![A_155, A_156]: (k2_xboole_0(k2_zfmisc_1(A_155, A_156), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_156, k1_xboole_0))), inference(resolution, [status(thm)], [c_1101, c_10])).
% 23.94/13.77  tff(c_248, plain, (![A_61, B_62]: (r1_tarski(A_61, k2_xboole_0(A_61, B_62)))), inference(resolution, [status(thm)], [c_6, c_232])).
% 23.94/13.77  tff(c_267, plain, (![A_3, B_4, B_62]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_62)))), inference(resolution, [status(thm)], [c_248, c_8])).
% 23.94/13.77  tff(c_1293, plain, (![A_155, A_156, B_62]: (r1_tarski(k2_zfmisc_1(A_155, A_156), k2_xboole_0(k1_xboole_0, B_62)) | ~r1_tarski(A_156, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1281, c_267])).
% 23.94/13.77  tff(c_1311, plain, (![A_155, A_156, B_62]: (r1_tarski(k2_zfmisc_1(A_155, A_156), B_62) | ~r1_tarski(A_156, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1293])).
% 23.94/13.77  tff(c_876, plain, (![A_120, C_121, B_122]: (r1_tarski(k2_zfmisc_1(A_120, C_121), k2_zfmisc_1(B_122, C_121)) | ~r1_tarski(A_120, B_122))), inference(cnfTransformation, [status(thm)], [f_53])).
% 23.94/13.77  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.94/13.77  tff(c_10710, plain, (![B_464, C_465, A_466]: (k2_zfmisc_1(B_464, C_465)=k2_zfmisc_1(A_466, C_465) | ~r1_tarski(k2_zfmisc_1(B_464, C_465), k2_zfmisc_1(A_466, C_465)) | ~r1_tarski(A_466, B_464))), inference(resolution, [status(thm)], [c_876, c_2])).
% 23.94/13.77  tff(c_39333, plain, (![A_955, A_954, A_953]: (k2_zfmisc_1(A_955, A_954)=k2_zfmisc_1(A_953, A_954) | ~r1_tarski(A_953, A_955) | ~r1_tarski(A_954, k1_xboole_0))), inference(resolution, [status(thm)], [c_1311, c_10710])).
% 23.94/13.77  tff(c_39517, plain, (![A_954]: (k2_zfmisc_1(k2_relat_1('#skF_2'), A_954)=k2_zfmisc_1('#skF_1', A_954) | ~r1_tarski(A_954, k1_xboole_0))), inference(resolution, [status(thm)], [c_56, c_39333])).
% 23.94/13.77  tff(c_18, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 23.94/13.77  tff(c_914, plain, (![A_123, B_124]: (r1_tarski(k2_zfmisc_1(A_123, B_124), k1_xboole_0) | ~r1_tarski(A_123, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_876])).
% 23.94/13.77  tff(c_1453, plain, (![A_167, B_168]: (k2_xboole_0(k2_zfmisc_1(A_167, B_168), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_167, k1_xboole_0))), inference(resolution, [status(thm)], [c_914, c_10])).
% 23.94/13.77  tff(c_1471, plain, (![A_167, B_168, B_62]: (r1_tarski(k2_zfmisc_1(A_167, B_168), k2_xboole_0(k1_xboole_0, B_62)) | ~r1_tarski(A_167, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1453, c_267])).
% 23.94/13.77  tff(c_1503, plain, (![A_169, B_170, B_171]: (r1_tarski(k2_zfmisc_1(A_169, B_170), B_171) | ~r1_tarski(A_169, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1471])).
% 23.94/13.77  tff(c_1563, plain, (![A_169, B_170, B_171]: (k2_xboole_0(k2_zfmisc_1(A_169, B_170), B_171)=B_171 | ~r1_tarski(A_169, k1_xboole_0))), inference(resolution, [status(thm)], [c_1503, c_10])).
% 23.94/13.77  tff(c_551, plain, (![B_92, A_93]: (r1_tarski(k1_relat_1(B_92), A_93) | ~v4_relat_1(B_92, A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.94/13.77  tff(c_2621, plain, (![B_215, A_216]: (k2_xboole_0(k1_relat_1(B_215), A_216)=A_216 | ~v4_relat_1(B_215, A_216) | ~v1_relat_1(B_215))), inference(resolution, [status(thm)], [c_551, c_10])).
% 23.94/13.77  tff(c_8466, plain, (![B_413, A_414, B_415]: (r1_tarski(k1_relat_1(B_413), k2_xboole_0(A_414, B_415)) | ~v4_relat_1(B_413, A_414) | ~v1_relat_1(B_413))), inference(superposition, [status(thm), theory('equality')], [c_2621, c_267])).
% 23.94/13.77  tff(c_28, plain, (![B_17, A_16]: (v4_relat_1(B_17, A_16) | ~r1_tarski(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.94/13.77  tff(c_8544, plain, (![B_413, A_414, B_415]: (v4_relat_1(B_413, k2_xboole_0(A_414, B_415)) | ~v4_relat_1(B_413, A_414) | ~v1_relat_1(B_413))), inference(resolution, [status(thm)], [c_8466, c_28])).
% 23.94/13.77  tff(c_30, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.94/13.77  tff(c_1495, plain, (![A_167, B_168, B_62]: (r1_tarski(k2_zfmisc_1(A_167, B_168), B_62) | ~r1_tarski(A_167, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1471])).
% 23.94/13.77  tff(c_11528, plain, (![C_487, B_488, A_489]: (k2_zfmisc_1(C_487, B_488)=k2_zfmisc_1(C_487, A_489) | ~r1_tarski(k2_zfmisc_1(C_487, B_488), k2_zfmisc_1(C_487, A_489)) | ~r1_tarski(A_489, B_488))), inference(resolution, [status(thm)], [c_1063, c_2])).
% 23.94/13.77  tff(c_43238, plain, (![A_975, B_976, A_977]: (k2_zfmisc_1(A_975, B_976)=k2_zfmisc_1(A_975, A_977) | ~r1_tarski(A_977, B_976) | ~r1_tarski(A_975, k1_xboole_0))), inference(resolution, [status(thm)], [c_1495, c_11528])).
% 23.94/13.77  tff(c_43433, plain, (![A_978]: (k2_zfmisc_1(A_978, k2_relat_1('#skF_2'))=k2_zfmisc_1(A_978, '#skF_1') | ~r1_tarski(A_978, k1_xboole_0))), inference(resolution, [status(thm)], [c_56, c_43238])).
% 23.94/13.77  tff(c_22, plain, (![A_11, C_13, B_12]: (r1_tarski(k2_zfmisc_1(A_11, C_13), k2_zfmisc_1(B_12, C_13)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 23.94/13.77  tff(c_14716, plain, (![A_574, C_575]: (r1_tarski(A_574, C_575) | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_574), k2_relat_1(A_574)), C_575) | ~v1_relat_1(A_574))), inference(superposition, [status(thm), theory('equality')], [c_6705, c_8])).
% 23.94/13.77  tff(c_14818, plain, (![A_574, B_12]: (r1_tarski(A_574, k2_zfmisc_1(B_12, k2_relat_1(A_574))) | ~v1_relat_1(A_574) | ~r1_tarski(k1_relat_1(A_574), B_12))), inference(resolution, [status(thm)], [c_22, c_14716])).
% 23.94/13.77  tff(c_43473, plain, (![A_978]: (r1_tarski('#skF_2', k2_zfmisc_1(A_978, '#skF_1')) | ~v1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), A_978) | ~r1_tarski(A_978, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_43433, c_14818])).
% 23.94/13.77  tff(c_59685, plain, (![A_1121]: (r1_tarski('#skF_2', k2_zfmisc_1(A_1121, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_1121) | ~r1_tarski(A_1121, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_43473])).
% 23.94/13.77  tff(c_59761, plain, (![A_16]: (r1_tarski('#skF_2', k2_zfmisc_1(A_16, '#skF_1')) | ~r1_tarski(A_16, k1_xboole_0) | ~v4_relat_1('#skF_2', A_16) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_59685])).
% 23.94/13.77  tff(c_59821, plain, (![A_1122]: (r1_tarski('#skF_2', k2_zfmisc_1(A_1122, '#skF_1')) | ~r1_tarski(A_1122, k1_xboole_0) | ~v4_relat_1('#skF_2', A_1122))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_59761])).
% 23.94/13.77  tff(c_327, plain, (![C_67, B_68, A_69]: (v5_relat_1(C_67, B_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 23.94/13.77  tff(c_338, plain, (![A_14, B_68, A_69]: (v5_relat_1(A_14, B_68) | ~r1_tarski(A_14, k2_zfmisc_1(A_69, B_68)))), inference(resolution, [status(thm)], [c_26, c_327])).
% 23.94/13.77  tff(c_44222, plain, (![A_14, A_978]: (v5_relat_1(A_14, k2_relat_1('#skF_2')) | ~r1_tarski(A_14, k2_zfmisc_1(A_978, '#skF_1')) | ~r1_tarski(A_978, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_43433, c_338])).
% 23.94/13.77  tff(c_59938, plain, (![A_1122]: (v5_relat_1('#skF_2', k2_relat_1('#skF_2')) | ~r1_tarski(A_1122, k1_xboole_0) | ~v4_relat_1('#skF_2', A_1122))), inference(resolution, [status(thm)], [c_59821, c_44222])).
% 23.94/13.77  tff(c_59984, plain, (![A_1123]: (~r1_tarski(A_1123, k1_xboole_0) | ~v4_relat_1('#skF_2', A_1123))), inference(splitLeft, [status(thm)], [c_59938])).
% 23.94/13.77  tff(c_60008, plain, (![A_414, B_415]: (~r1_tarski(k2_xboole_0(A_414, B_415), k1_xboole_0) | ~v4_relat_1('#skF_2', A_414) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_8544, c_59984])).
% 23.94/13.77  tff(c_60316, plain, (![A_1127, B_1128]: (~r1_tarski(k2_xboole_0(A_1127, B_1128), k1_xboole_0) | ~v4_relat_1('#skF_2', A_1127))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60008])).
% 23.94/13.77  tff(c_60391, plain, (![B_171, A_169, B_170]: (~r1_tarski(B_171, k1_xboole_0) | ~v4_relat_1('#skF_2', k2_zfmisc_1(A_169, B_170)) | ~r1_tarski(A_169, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1563, c_60316])).
% 23.94/13.77  tff(c_61318, plain, (![A_1150, B_1151]: (~v4_relat_1('#skF_2', k2_zfmisc_1(A_1150, B_1151)) | ~r1_tarski(A_1150, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_60391])).
% 23.94/13.77  tff(c_61348, plain, (![A_954]: (~v4_relat_1('#skF_2', k2_zfmisc_1('#skF_1', A_954)) | ~r1_tarski(k2_relat_1('#skF_2'), k1_xboole_0) | ~r1_tarski(A_954, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_39517, c_61318])).
% 23.94/13.77  tff(c_61433, plain, (~r1_tarski(k2_relat_1('#skF_2'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_61348])).
% 23.94/13.77  tff(c_66867, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66863, c_61433])).
% 23.94/13.77  tff(c_67117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_66867])).
% 23.94/13.77  tff(c_67119, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_61348])).
% 23.94/13.77  tff(c_1318, plain, (![A_157, A_158, B_159]: (r1_tarski(k2_zfmisc_1(A_157, A_158), B_159) | ~r1_tarski(A_158, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1293])).
% 23.94/13.77  tff(c_1378, plain, (![A_157, A_158, B_159]: (k2_xboole_0(k2_zfmisc_1(A_157, A_158), B_159)=B_159 | ~r1_tarski(A_158, k1_xboole_0))), inference(resolution, [status(thm)], [c_1318, c_10])).
% 23.94/13.77  tff(c_11283, plain, (![A_479, B_480]: (r1_tarski(A_479, k2_xboole_0(k2_zfmisc_1(k1_relat_1(A_479), k2_relat_1(A_479)), B_480)) | ~v1_relat_1(A_479))), inference(superposition, [status(thm), theory('equality')], [c_6705, c_267])).
% 23.94/13.77  tff(c_11344, plain, (![A_479, B_159]: (r1_tarski(A_479, B_159) | ~v1_relat_1(A_479) | ~r1_tarski(k2_relat_1(A_479), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1378, c_11283])).
% 23.94/13.77  tff(c_67236, plain, (![B_159]: (r1_tarski('#skF_2', B_159) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_67119, c_11344])).
% 23.94/13.77  tff(c_67305, plain, (![B_159]: (r1_tarski('#skF_2', B_159))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_67236])).
% 23.94/13.77  tff(c_689, plain, (![C_104, A_105, B_106]: (v4_relat_1(C_104, A_105) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 23.94/13.77  tff(c_701, plain, (![C_107, A_108]: (v4_relat_1(C_107, A_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_689])).
% 23.94/13.77  tff(c_705, plain, (![A_14, A_108]: (v4_relat_1(A_14, A_108) | ~r1_tarski(A_14, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_701])).
% 23.94/13.77  tff(c_8535, plain, (![B_413, A_8]: (r1_tarski(k1_relat_1(B_413), A_8) | ~v4_relat_1(B_413, k1_xboole_0) | ~v1_relat_1(B_413))), inference(superposition, [status(thm), theory('equality')], [c_104, c_8466])).
% 23.94/13.77  tff(c_32, plain, (![A_18]: (r1_tarski(A_18, k2_zfmisc_1(k1_relat_1(A_18), k2_relat_1(A_18))) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 23.94/13.77  tff(c_44216, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')) | ~v1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_43433, c_32])).
% 23.94/13.77  tff(c_44335, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_44216])).
% 23.94/13.77  tff(c_44346, plain, (~r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_44335])).
% 23.94/13.77  tff(c_44352, plain, (~v4_relat_1('#skF_2', k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8535, c_44346])).
% 23.94/13.77  tff(c_44361, plain, (~v4_relat_1('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_44352])).
% 23.94/13.77  tff(c_44368, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_705, c_44361])).
% 23.94/13.77  tff(c_67326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67305, c_44368])).
% 23.94/13.77  tff(c_67328, plain, (r1_tarski(k1_relat_1('#skF_2'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_44335])).
% 23.94/13.77  tff(c_11348, plain, (![A_479, B_171]: (r1_tarski(A_479, B_171) | ~v1_relat_1(A_479) | ~r1_tarski(k1_relat_1(A_479), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1563, c_11283])).
% 23.94/13.77  tff(c_68185, plain, (![B_171]: (r1_tarski('#skF_2', B_171) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_67328, c_11348])).
% 23.94/13.77  tff(c_68264, plain, (![B_1217]: (r1_tarski('#skF_2', B_1217))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_68185])).
% 23.94/13.77  tff(c_143, plain, (![B_43, A_44]: (B_43=A_44 | ~r1_tarski(B_43, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.94/13.77  tff(c_155, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_143])).
% 23.94/13.77  tff(c_68431, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_68264, c_155])).
% 23.94/13.77  tff(c_169, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 23.94/13.77  tff(c_179, plain, (![C_49]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_169])).
% 23.94/13.77  tff(c_185, plain, (![A_50]: (v1_relat_1(A_50) | ~r1_tarski(A_50, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_179])).
% 23.94/13.77  tff(c_194, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_185])).
% 23.94/13.77  tff(c_42, plain, (![A_28]: (v1_funct_2(k1_xboole_0, A_28, k1_xboole_0) | k1_xboole_0=A_28 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_28, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 23.94/13.77  tff(c_66, plain, (![A_28]: (v1_funct_2(k1_xboole_0, A_28, k1_xboole_0) | k1_xboole_0=A_28 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_42])).
% 23.94/13.77  tff(c_712, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_66])).
% 23.94/13.77  tff(c_715, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_712])).
% 23.94/13.77  tff(c_719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_715])).
% 23.94/13.77  tff(c_721, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_66])).
% 23.94/13.77  tff(c_696, plain, (![C_104, A_9]: (v4_relat_1(C_104, A_9) | ~m1_subset_1(C_104, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_689])).
% 23.94/13.77  tff(c_739, plain, (![A_111]: (v4_relat_1(k1_xboole_0, A_111))), inference(resolution, [status(thm)], [c_721, c_696])).
% 23.94/13.77  tff(c_576, plain, (![B_92]: (k1_relat_1(B_92)=k1_xboole_0 | ~v4_relat_1(B_92, k1_xboole_0) | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_551, c_155])).
% 23.94/13.77  tff(c_743, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_739, c_576])).
% 23.94/13.77  tff(c_746, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_194, c_743])).
% 23.94/13.77  tff(c_2690, plain, (![B_217, C_218]: (k1_relset_1(k1_xboole_0, B_217, C_218)=k1_relat_1(C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1567])).
% 23.94/13.77  tff(c_2692, plain, (![B_217]: (k1_relset_1(k1_xboole_0, B_217, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_721, c_2690])).
% 23.94/13.77  tff(c_2697, plain, (![B_217]: (k1_relset_1(k1_xboole_0, B_217, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_746, c_2692])).
% 23.94/13.77  tff(c_46, plain, (![C_30, B_29]: (v1_funct_2(C_30, k1_xboole_0, B_29) | k1_relset_1(k1_xboole_0, B_29, C_30)!=k1_xboole_0 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_29))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 23.94/13.77  tff(c_2423, plain, (![C_199, B_200]: (v1_funct_2(C_199, k1_xboole_0, B_200) | k1_relset_1(k1_xboole_0, B_200, C_199)!=k1_xboole_0 | ~m1_subset_1(C_199, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_46])).
% 23.94/13.77  tff(c_2429, plain, (![B_200]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_200) | k1_relset_1(k1_xboole_0, B_200, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_721, c_2423])).
% 23.94/13.77  tff(c_2700, plain, (![B_200]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_200))), inference(demodulation, [status(thm), theory('equality')], [c_2697, c_2429])).
% 23.94/13.77  tff(c_68700, plain, (![B_200]: (v1_funct_2('#skF_2', '#skF_2', B_200))), inference(demodulation, [status(thm), theory('equality')], [c_68431, c_68431, c_2700])).
% 23.94/13.77  tff(c_68211, plain, (k1_relat_1('#skF_2')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_67328, c_2])).
% 23.94/13.77  tff(c_68262, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_68211])).
% 23.94/13.77  tff(c_68752, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68431, c_68262])).
% 23.94/13.77  tff(c_68754, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68752, c_296])).
% 23.94/13.77  tff(c_69896, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68700, c_68754])).
% 23.94/13.77  tff(c_69897, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_62])).
% 23.94/13.77  tff(c_69902, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_69897])).
% 23.94/13.77  tff(c_105240, plain, (~v1_relat_1('#skF_2') | ~r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_105158, c_69902])).
% 23.94/13.77  tff(c_105368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_105240])).
% 23.94/13.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.94/13.77  
% 23.94/13.77  Inference rules
% 23.94/13.77  ----------------------
% 23.94/13.77  #Ref     : 0
% 23.94/13.77  #Sup     : 26371
% 23.94/13.77  #Fact    : 0
% 23.94/13.77  #Define  : 0
% 23.94/13.77  #Split   : 26
% 23.94/13.77  #Chain   : 0
% 23.94/13.77  #Close   : 0
% 23.94/13.77  
% 23.94/13.77  Ordering : KBO
% 23.94/13.77  
% 23.94/13.77  Simplification rules
% 23.94/13.77  ----------------------
% 23.94/13.77  #Subsume      : 7504
% 23.94/13.77  #Demod        : 26254
% 23.94/13.77  #Tautology    : 12042
% 23.94/13.77  #SimpNegUnit  : 21
% 23.94/13.77  #BackRed      : 449
% 23.94/13.77  
% 23.94/13.77  #Partial instantiations: 0
% 23.94/13.77  #Strategies tried      : 1
% 23.94/13.77  
% 23.94/13.77  Timing (in seconds)
% 23.94/13.77  ----------------------
% 24.20/13.77  Preprocessing        : 0.34
% 24.20/13.77  Parsing              : 0.18
% 24.20/13.77  CNF conversion       : 0.02
% 24.20/13.77  Main loop            : 12.64
% 24.20/13.77  Inferencing          : 2.14
% 24.20/13.77  Reduction            : 4.68
% 24.20/13.77  Demodulation         : 3.70
% 24.20/13.77  BG Simplification    : 0.23
% 24.20/13.77  Subsumption          : 5.04
% 24.20/13.77  Abstraction          : 0.38
% 24.20/13.77  MUC search           : 0.00
% 24.20/13.77  Cooper               : 0.00
% 24.20/13.77  Total                : 13.03
% 24.20/13.77  Index Insertion      : 0.00
% 24.20/13.77  Index Deletion       : 0.00
% 24.20/13.77  Index Matching       : 0.00
% 24.20/13.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
