%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:41 EST 2020

% Result     : Theorem 4.37s
% Output     : CNFRefutation 4.73s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 152 expanded)
%              Number of leaves         :   31 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :  161 ( 385 expanded)
%              Number of equality atoms :   24 (  53 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
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

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_16,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2156,plain,(
    ! [C_208,A_209,B_210] :
      ( m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210)))
      | ~ r1_tarski(k2_relat_1(C_208),B_210)
      | ~ r1_tarski(k1_relat_1(C_208),A_209)
      | ~ v1_relat_1(C_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_18,plain,(
    ! [A_10] :
      ( v1_xboole_0(k1_relat_1(A_10))
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_442,plain,(
    ! [C_81,A_82,B_83] :
      ( m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ r1_tarski(k2_relat_1(C_81),B_83)
      | ~ r1_tarski(k1_relat_1(C_81),A_82)
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    ! [C_30,A_27,B_28] :
      ( v1_partfun1(C_30,A_27)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_597,plain,(
    ! [C_96,A_97,B_98] :
      ( v1_partfun1(C_96,A_97)
      | ~ v1_xboole_0(A_97)
      | ~ r1_tarski(k2_relat_1(C_96),B_98)
      | ~ r1_tarski(k1_relat_1(C_96),A_97)
      | ~ v1_relat_1(C_96) ) ),
    inference(resolution,[status(thm)],[c_442,c_32])).

tff(c_601,plain,(
    ! [C_99,A_100] :
      ( v1_partfun1(C_99,A_100)
      | ~ v1_xboole_0(A_100)
      | ~ r1_tarski(k1_relat_1(C_99),A_100)
      | ~ v1_relat_1(C_99) ) ),
    inference(resolution,[status(thm)],[c_16,c_597])).

tff(c_621,plain,(
    ! [C_99] :
      ( v1_partfun1(C_99,k1_relat_1(C_99))
      | ~ v1_xboole_0(k1_relat_1(C_99))
      | ~ v1_relat_1(C_99) ) ),
    inference(resolution,[status(thm)],[c_16,c_601])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_28,plain,(
    ! [C_26,A_24,B_25] :
      ( v1_funct_2(C_26,A_24,B_25)
      | ~ v1_partfun1(C_26,A_24)
      | ~ v1_funct_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1211,plain,(
    ! [C_137,A_138,B_139] :
      ( v1_funct_2(C_137,A_138,B_139)
      | ~ v1_partfun1(C_137,A_138)
      | ~ v1_funct_1(C_137)
      | ~ r1_tarski(k2_relat_1(C_137),B_139)
      | ~ r1_tarski(k1_relat_1(C_137),A_138)
      | ~ v1_relat_1(C_137) ) ),
    inference(resolution,[status(thm)],[c_442,c_28])).

tff(c_1246,plain,(
    ! [C_141,A_142] :
      ( v1_funct_2(C_141,A_142,k2_relat_1(C_141))
      | ~ v1_partfun1(C_141,A_142)
      | ~ v1_funct_1(C_141)
      | ~ r1_tarski(k1_relat_1(C_141),A_142)
      | ~ v1_relat_1(C_141) ) ),
    inference(resolution,[status(thm)],[c_16,c_1211])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_85,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_1249,plain,
    ( ~ v1_partfun1('#skF_4',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1246,c_85])).

tff(c_1252,plain,(
    ~ v1_partfun1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16,c_48,c_1249])).

tff(c_1255,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_621,c_1252])).

tff(c_1258,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1255])).

tff(c_1262,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_1258])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    ! [A_18,B_19,C_20] :
      ( k1_relset_1(A_18,B_19,C_20) = k1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_847,plain,(
    ! [A_112,B_113,C_114] :
      ( k1_relset_1(A_112,B_113,C_114) = k1_relat_1(C_114)
      | ~ r1_tarski(k2_relat_1(C_114),B_113)
      | ~ r1_tarski(k1_relat_1(C_114),A_112)
      | ~ v1_relat_1(C_114) ) ),
    inference(resolution,[status(thm)],[c_442,c_24])).

tff(c_852,plain,(
    ! [A_115,C_116] :
      ( k1_relset_1(A_115,k2_relat_1(C_116),C_116) = k1_relat_1(C_116)
      | ~ r1_tarski(k1_relat_1(C_116),A_115)
      | ~ v1_relat_1(C_116) ) ),
    inference(resolution,[status(thm)],[c_16,c_847])).

tff(c_869,plain,(
    ! [C_116] :
      ( k1_relset_1(k1_relat_1(C_116),k2_relat_1(C_116),C_116) = k1_relat_1(C_116)
      | ~ v1_relat_1(C_116) ) ),
    inference(resolution,[status(thm)],[c_16,c_852])).

tff(c_26,plain,(
    ! [C_23,A_21,B_22] :
      ( m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ r1_tarski(k2_relat_1(C_23),B_22)
      | ~ r1_tarski(k1_relat_1(C_23),A_21)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_622,plain,(
    ! [B_101,C_102,A_103] :
      ( k1_xboole_0 = B_101
      | v1_funct_2(C_102,A_103,B_101)
      | k1_relset_1(A_103,B_101,C_102) != A_103
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1491,plain,(
    ! [B_159,C_160,A_161] :
      ( k1_xboole_0 = B_159
      | v1_funct_2(C_160,A_161,B_159)
      | k1_relset_1(A_161,B_159,C_160) != A_161
      | ~ r1_tarski(k2_relat_1(C_160),B_159)
      | ~ r1_tarski(k1_relat_1(C_160),A_161)
      | ~ v1_relat_1(C_160) ) ),
    inference(resolution,[status(thm)],[c_26,c_622])).

tff(c_1549,plain,(
    ! [C_164,A_165] :
      ( k2_relat_1(C_164) = k1_xboole_0
      | v1_funct_2(C_164,A_165,k2_relat_1(C_164))
      | k1_relset_1(A_165,k2_relat_1(C_164),C_164) != A_165
      | ~ r1_tarski(k1_relat_1(C_164),A_165)
      | ~ v1_relat_1(C_164) ) ),
    inference(resolution,[status(thm)],[c_16,c_1491])).

tff(c_1558,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1549,c_85])).

tff(c_1565,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16,c_1558])).

tff(c_1566,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1565])).

tff(c_1569,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_869,c_1566])).

tff(c_1573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1569])).

tff(c_1574,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1565])).

tff(c_22,plain,(
    ! [C_17,B_15,A_14] :
      ( v1_xboole_0(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(B_15,A_14)))
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_480,plain,(
    ! [C_84,B_85,A_86] :
      ( v1_xboole_0(C_84)
      | ~ v1_xboole_0(B_85)
      | ~ r1_tarski(k2_relat_1(C_84),B_85)
      | ~ r1_tarski(k1_relat_1(C_84),A_86)
      | ~ v1_relat_1(C_84) ) ),
    inference(resolution,[status(thm)],[c_442,c_22])).

tff(c_485,plain,(
    ! [C_87,A_88] :
      ( v1_xboole_0(C_87)
      | ~ v1_xboole_0(k2_relat_1(C_87))
      | ~ r1_tarski(k1_relat_1(C_87),A_88)
      | ~ v1_relat_1(C_87) ) ),
    inference(resolution,[status(thm)],[c_16,c_480])).

tff(c_505,plain,(
    ! [C_87] :
      ( v1_xboole_0(C_87)
      | ~ v1_xboole_0(k2_relat_1(C_87))
      | ~ v1_relat_1(C_87) ) ),
    inference(resolution,[status(thm)],[c_16,c_485])).

tff(c_1639,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1574,c_505])).

tff(c_1705,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6,c_1639])).

tff(c_1707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1262,c_1705])).

tff(c_1708,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2187,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2156,c_1708])).

tff(c_2200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16,c_16,c_2187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.37/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/1.89  
% 4.37/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/1.90  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 4.37/1.90  
% 4.37/1.90  %Foreground sorts:
% 4.37/1.90  
% 4.37/1.90  
% 4.37/1.90  %Background operators:
% 4.37/1.90  
% 4.37/1.90  
% 4.37/1.90  %Foreground operators:
% 4.37/1.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.37/1.90  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.37/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.37/1.90  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.37/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.37/1.90  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.37/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.37/1.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.37/1.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.37/1.90  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.37/1.90  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.37/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.37/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.37/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.37/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.37/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.37/1.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.37/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.37/1.90  
% 4.73/1.91  tff(f_128, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 4.73/1.91  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.73/1.91  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 4.73/1.91  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 4.73/1.91  tff(f_99, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 4.73/1.91  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 4.73/1.91  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.73/1.91  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.73/1.91  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.73/1.91  tff(f_70, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.73/1.91  tff(c_50, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.73/1.91  tff(c_16, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.73/1.91  tff(c_2156, plain, (![C_208, A_209, B_210]: (m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))) | ~r1_tarski(k2_relat_1(C_208), B_210) | ~r1_tarski(k1_relat_1(C_208), A_209) | ~v1_relat_1(C_208))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.73/1.91  tff(c_18, plain, (![A_10]: (v1_xboole_0(k1_relat_1(A_10)) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.73/1.91  tff(c_442, plain, (![C_81, A_82, B_83]: (m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~r1_tarski(k2_relat_1(C_81), B_83) | ~r1_tarski(k1_relat_1(C_81), A_82) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.73/1.91  tff(c_32, plain, (![C_30, A_27, B_28]: (v1_partfun1(C_30, A_27) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.73/1.91  tff(c_597, plain, (![C_96, A_97, B_98]: (v1_partfun1(C_96, A_97) | ~v1_xboole_0(A_97) | ~r1_tarski(k2_relat_1(C_96), B_98) | ~r1_tarski(k1_relat_1(C_96), A_97) | ~v1_relat_1(C_96))), inference(resolution, [status(thm)], [c_442, c_32])).
% 4.73/1.91  tff(c_601, plain, (![C_99, A_100]: (v1_partfun1(C_99, A_100) | ~v1_xboole_0(A_100) | ~r1_tarski(k1_relat_1(C_99), A_100) | ~v1_relat_1(C_99))), inference(resolution, [status(thm)], [c_16, c_597])).
% 4.73/1.91  tff(c_621, plain, (![C_99]: (v1_partfun1(C_99, k1_relat_1(C_99)) | ~v1_xboole_0(k1_relat_1(C_99)) | ~v1_relat_1(C_99))), inference(resolution, [status(thm)], [c_16, c_601])).
% 4.73/1.91  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.73/1.91  tff(c_28, plain, (![C_26, A_24, B_25]: (v1_funct_2(C_26, A_24, B_25) | ~v1_partfun1(C_26, A_24) | ~v1_funct_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.73/1.91  tff(c_1211, plain, (![C_137, A_138, B_139]: (v1_funct_2(C_137, A_138, B_139) | ~v1_partfun1(C_137, A_138) | ~v1_funct_1(C_137) | ~r1_tarski(k2_relat_1(C_137), B_139) | ~r1_tarski(k1_relat_1(C_137), A_138) | ~v1_relat_1(C_137))), inference(resolution, [status(thm)], [c_442, c_28])).
% 4.73/1.91  tff(c_1246, plain, (![C_141, A_142]: (v1_funct_2(C_141, A_142, k2_relat_1(C_141)) | ~v1_partfun1(C_141, A_142) | ~v1_funct_1(C_141) | ~r1_tarski(k1_relat_1(C_141), A_142) | ~v1_relat_1(C_141))), inference(resolution, [status(thm)], [c_16, c_1211])).
% 4.73/1.91  tff(c_46, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.73/1.91  tff(c_52, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 4.73/1.91  tff(c_85, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_52])).
% 4.73/1.91  tff(c_1249, plain, (~v1_partfun1('#skF_4', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1246, c_85])).
% 4.73/1.91  tff(c_1252, plain, (~v1_partfun1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_16, c_48, c_1249])).
% 4.73/1.91  tff(c_1255, plain, (~v1_xboole_0(k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_621, c_1252])).
% 4.73/1.91  tff(c_1258, plain, (~v1_xboole_0(k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1255])).
% 4.73/1.91  tff(c_1262, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_18, c_1258])).
% 4.73/1.91  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.73/1.91  tff(c_24, plain, (![A_18, B_19, C_20]: (k1_relset_1(A_18, B_19, C_20)=k1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.73/1.91  tff(c_847, plain, (![A_112, B_113, C_114]: (k1_relset_1(A_112, B_113, C_114)=k1_relat_1(C_114) | ~r1_tarski(k2_relat_1(C_114), B_113) | ~r1_tarski(k1_relat_1(C_114), A_112) | ~v1_relat_1(C_114))), inference(resolution, [status(thm)], [c_442, c_24])).
% 4.73/1.91  tff(c_852, plain, (![A_115, C_116]: (k1_relset_1(A_115, k2_relat_1(C_116), C_116)=k1_relat_1(C_116) | ~r1_tarski(k1_relat_1(C_116), A_115) | ~v1_relat_1(C_116))), inference(resolution, [status(thm)], [c_16, c_847])).
% 4.73/1.91  tff(c_869, plain, (![C_116]: (k1_relset_1(k1_relat_1(C_116), k2_relat_1(C_116), C_116)=k1_relat_1(C_116) | ~v1_relat_1(C_116))), inference(resolution, [status(thm)], [c_16, c_852])).
% 4.73/1.91  tff(c_26, plain, (![C_23, A_21, B_22]: (m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~r1_tarski(k2_relat_1(C_23), B_22) | ~r1_tarski(k1_relat_1(C_23), A_21) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.73/1.91  tff(c_622, plain, (![B_101, C_102, A_103]: (k1_xboole_0=B_101 | v1_funct_2(C_102, A_103, B_101) | k1_relset_1(A_103, B_101, C_102)!=A_103 | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_101))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.73/1.91  tff(c_1491, plain, (![B_159, C_160, A_161]: (k1_xboole_0=B_159 | v1_funct_2(C_160, A_161, B_159) | k1_relset_1(A_161, B_159, C_160)!=A_161 | ~r1_tarski(k2_relat_1(C_160), B_159) | ~r1_tarski(k1_relat_1(C_160), A_161) | ~v1_relat_1(C_160))), inference(resolution, [status(thm)], [c_26, c_622])).
% 4.73/1.91  tff(c_1549, plain, (![C_164, A_165]: (k2_relat_1(C_164)=k1_xboole_0 | v1_funct_2(C_164, A_165, k2_relat_1(C_164)) | k1_relset_1(A_165, k2_relat_1(C_164), C_164)!=A_165 | ~r1_tarski(k1_relat_1(C_164), A_165) | ~v1_relat_1(C_164))), inference(resolution, [status(thm)], [c_16, c_1491])).
% 4.73/1.91  tff(c_1558, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1549, c_85])).
% 4.73/1.91  tff(c_1565, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_16, c_1558])).
% 4.73/1.91  tff(c_1566, plain, (k1_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1565])).
% 4.73/1.91  tff(c_1569, plain, (~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_869, c_1566])).
% 4.73/1.91  tff(c_1573, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1569])).
% 4.73/1.91  tff(c_1574, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1565])).
% 4.73/1.91  tff(c_22, plain, (![C_17, B_15, A_14]: (v1_xboole_0(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(B_15, A_14))) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.73/1.91  tff(c_480, plain, (![C_84, B_85, A_86]: (v1_xboole_0(C_84) | ~v1_xboole_0(B_85) | ~r1_tarski(k2_relat_1(C_84), B_85) | ~r1_tarski(k1_relat_1(C_84), A_86) | ~v1_relat_1(C_84))), inference(resolution, [status(thm)], [c_442, c_22])).
% 4.73/1.91  tff(c_485, plain, (![C_87, A_88]: (v1_xboole_0(C_87) | ~v1_xboole_0(k2_relat_1(C_87)) | ~r1_tarski(k1_relat_1(C_87), A_88) | ~v1_relat_1(C_87))), inference(resolution, [status(thm)], [c_16, c_480])).
% 4.73/1.91  tff(c_505, plain, (![C_87]: (v1_xboole_0(C_87) | ~v1_xboole_0(k2_relat_1(C_87)) | ~v1_relat_1(C_87))), inference(resolution, [status(thm)], [c_16, c_485])).
% 4.73/1.91  tff(c_1639, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1574, c_505])).
% 4.73/1.91  tff(c_1705, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6, c_1639])).
% 4.73/1.91  tff(c_1707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1262, c_1705])).
% 4.73/1.91  tff(c_1708, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))))), inference(splitRight, [status(thm)], [c_52])).
% 4.73/1.91  tff(c_2187, plain, (~r1_tarski(k2_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2156, c_1708])).
% 4.73/1.91  tff(c_2200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_16, c_16, c_2187])).
% 4.73/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.91  
% 4.73/1.91  Inference rules
% 4.73/1.91  ----------------------
% 4.73/1.91  #Ref     : 0
% 4.73/1.91  #Sup     : 520
% 4.73/1.91  #Fact    : 0
% 4.73/1.91  #Define  : 0
% 4.73/1.91  #Split   : 10
% 4.73/1.91  #Chain   : 0
% 4.73/1.91  #Close   : 0
% 4.73/1.91  
% 4.73/1.91  Ordering : KBO
% 4.73/1.91  
% 4.73/1.91  Simplification rules
% 4.73/1.91  ----------------------
% 4.73/1.91  #Subsume      : 196
% 4.73/1.91  #Demod        : 272
% 4.73/1.91  #Tautology    : 98
% 4.73/1.91  #SimpNegUnit  : 1
% 4.73/1.91  #BackRed      : 1
% 4.73/1.91  
% 4.73/1.91  #Partial instantiations: 0
% 4.73/1.91  #Strategies tried      : 1
% 4.73/1.91  
% 4.73/1.91  Timing (in seconds)
% 4.73/1.91  ----------------------
% 4.73/1.91  Preprocessing        : 0.34
% 4.73/1.91  Parsing              : 0.16
% 4.73/1.91  CNF conversion       : 0.03
% 4.73/1.91  Main loop            : 0.74
% 4.73/1.91  Inferencing          : 0.24
% 4.73/1.91  Reduction            : 0.20
% 4.73/1.91  Demodulation         : 0.14
% 4.73/1.91  BG Simplification    : 0.03
% 4.73/1.91  Subsumption          : 0.22
% 4.73/1.91  Abstraction          : 0.04
% 4.73/1.91  MUC search           : 0.00
% 4.73/1.92  Cooper               : 0.00
% 4.73/1.92  Total                : 1.12
% 4.73/1.92  Index Insertion      : 0.00
% 4.73/1.92  Index Deletion       : 0.00
% 4.73/1.92  Index Matching       : 0.00
% 4.73/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
