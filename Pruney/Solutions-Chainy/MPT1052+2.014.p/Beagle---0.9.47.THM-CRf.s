%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:10 EST 2020

% Result     : Theorem 10.27s
% Output     : CNFRefutation 10.43s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 749 expanded)
%              Number of leaves         :   42 ( 254 expanded)
%              Depth                    :   15
%              Number of atoms          :  324 (1645 expanded)
%              Number of equality atoms :  124 ( 495 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

tff(f_147,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_134,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( r1_tarski(k6_relat_1(B),C)
       => ( B = k1_relset_1(B,A,C)
          & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_119,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(c_225,plain,(
    ! [A_59,B_60] :
      ( v1_xboole_0(k1_funct_2(A_59,B_60))
      | ~ v1_xboole_0(B_60)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_72,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_105,plain,(
    ! [B_44,A_45] :
      ( ~ r2_hidden(B_44,A_45)
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_105])).

tff(c_232,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_225,c_109])).

tff(c_255,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_70,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_159,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_287,plain,(
    ! [A_66,B_67] :
      ( k1_funct_2(A_66,B_67) = k1_xboole_0
      | ~ v1_xboole_0(B_67)
      | v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_225,c_8])).

tff(c_294,plain,(
    ! [A_68] :
      ( k1_funct_2(A_68,k1_xboole_0) = k1_xboole_0
      | v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_6,c_287])).

tff(c_307,plain,(
    k1_funct_2('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_294,c_255])).

tff(c_459,plain,(
    ! [C_89,A_90,B_91] :
      ( m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ r2_hidden(C_89,k1_funct_2(A_90,B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_472,plain,(
    ! [C_94,A_95,B_96] :
      ( r1_tarski(C_94,k2_zfmisc_1(A_95,B_96))
      | ~ r2_hidden(C_94,k1_funct_2(A_95,B_96)) ) ),
    inference(resolution,[status(thm)],[c_459,c_12])).

tff(c_481,plain,(
    ! [C_94] :
      ( r1_tarski(C_94,k2_zfmisc_1('#skF_3',k1_xboole_0))
      | ~ r2_hidden(C_94,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_472])).

tff(c_38,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,(
    ! [A_18] : k2_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_115,plain,(
    ! [A_47] :
      ( k2_relat_1(A_47) != k1_xboole_0
      | k1_xboole_0 = A_47
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_121,plain,(
    ! [A_19] :
      ( k2_relat_1(k6_relat_1(A_19)) != k1_xboole_0
      | k6_relat_1(A_19) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_115])).

tff(c_127,plain,(
    ! [A_19] :
      ( k1_xboole_0 != A_19
      | k6_relat_1(A_19) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_121])).

tff(c_1163,plain,(
    ! [A_129,B_130] :
      ( r1_tarski(k1_relat_1(A_129),k1_relat_1(B_130))
      | ~ r1_tarski(A_129,B_130)
      | ~ v1_relat_1(B_130)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1172,plain,(
    ! [A_18,B_130] :
      ( r1_tarski(A_18,k1_relat_1(B_130))
      | ~ r1_tarski(k6_relat_1(A_18),B_130)
      | ~ v1_relat_1(B_130)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1163])).

tff(c_1184,plain,(
    ! [A_131,B_132] :
      ( r1_tarski(A_131,k1_relat_1(B_132))
      | ~ r1_tarski(k6_relat_1(A_131),B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1172])).

tff(c_1199,plain,(
    ! [A_19,B_132] :
      ( r1_tarski(A_19,k1_relat_1(B_132))
      | ~ r1_tarski(k1_xboole_0,B_132)
      | ~ v1_relat_1(B_132)
      | k1_xboole_0 != A_19 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_1184])).

tff(c_1212,plain,(
    ! [A_133,B_134] :
      ( r1_tarski(A_133,k1_relat_1(B_134))
      | ~ v1_relat_1(B_134)
      | k1_xboole_0 != A_133 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1199])).

tff(c_1222,plain,(
    ! [A_133,A_18] :
      ( r1_tarski(A_133,A_18)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | k1_xboole_0 != A_133 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1212])).

tff(c_1228,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1222])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1923,plain,(
    ! [B_194,A_195,C_196] :
      ( k1_relset_1(B_194,A_195,C_196) = B_194
      | ~ r1_tarski(k6_relat_1(B_194),C_196)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(B_194,A_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3160,plain,(
    ! [B_1721,A_1722,A_1723] :
      ( k1_relset_1(B_1721,A_1722,A_1723) = B_1721
      | ~ r1_tarski(k6_relat_1(B_1721),A_1723)
      | ~ r1_tarski(A_1723,k2_zfmisc_1(B_1721,A_1722)) ) ),
    inference(resolution,[status(thm)],[c_14,c_1923])).

tff(c_3207,plain,(
    ! [A_19,A_1722,A_1723] :
      ( k1_relset_1(A_19,A_1722,A_1723) = A_19
      | ~ r1_tarski(k1_xboole_0,A_1723)
      | ~ r1_tarski(A_1723,k2_zfmisc_1(A_19,A_1722))
      | k1_xboole_0 != A_19 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_3160])).

tff(c_3353,plain,(
    ! [A_1728,A_1729,A_1730] :
      ( k1_relset_1(A_1728,A_1729,A_1730) = A_1728
      | ~ r1_tarski(A_1730,k2_zfmisc_1(A_1728,A_1729))
      | k1_xboole_0 != A_1728 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1228,c_3207])).

tff(c_3416,plain,(
    ! [C_94] :
      ( k1_relset_1('#skF_3',k1_xboole_0,C_94) = '#skF_3'
      | k1_xboole_0 != '#skF_3'
      | ~ r2_hidden(C_94,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_481,c_3353])).

tff(c_3792,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3416])).

tff(c_277,plain,(
    ! [C_63,A_64,B_65] :
      ( v1_funct_2(C_63,A_64,B_65)
      | ~ r2_hidden(C_63,k1_funct_2(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_286,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_277])).

tff(c_62,plain,(
    ! [C_33,A_31,B_32] :
      ( m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ r2_hidden(C_33,k1_funct_2(A_31,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_594,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1000,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ r2_hidden(C_112,k1_funct_2(A_110,B_111)) ) ),
    inference(resolution,[status(thm)],[c_62,c_594])).

tff(c_1039,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1000])).

tff(c_3012,plain,(
    ! [B_1707,A_1708,C_1709] :
      ( k1_xboole_0 = B_1707
      | k1_relset_1(A_1708,B_1707,C_1709) = A_1708
      | ~ v1_funct_2(C_1709,A_1708,B_1707)
      | ~ m1_subset_1(C_1709,k1_zfmisc_1(k2_zfmisc_1(A_1708,B_1707))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_8324,plain,(
    ! [B_1849,A_1850,C_1851] :
      ( k1_xboole_0 = B_1849
      | k1_relset_1(A_1850,B_1849,C_1851) = A_1850
      | ~ v1_funct_2(C_1851,A_1850,B_1849)
      | ~ r2_hidden(C_1851,k1_funct_2(A_1850,B_1849)) ) ),
    inference(resolution,[status(thm)],[c_62,c_3012])).

tff(c_8406,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_8324])).

tff(c_8419,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_1039,c_8406])).

tff(c_8421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_3792,c_8419])).

tff(c_8423,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3416])).

tff(c_8536,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8423,c_6])).

tff(c_8538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_8536])).

tff(c_8540,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_8548,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8540,c_8])).

tff(c_8539,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_8544,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8539,c_8])).

tff(c_8567,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8548,c_8544])).

tff(c_8574,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8567,c_159])).

tff(c_8576,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8567,c_72])).

tff(c_9003,plain,(
    ! [C_1888,A_1889,B_1890] :
      ( m1_subset_1(C_1888,k1_zfmisc_1(k2_zfmisc_1(A_1889,B_1890)))
      | ~ r2_hidden(C_1888,k1_funct_2(A_1889,B_1890)) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_9008,plain,(
    ! [C_1891,A_1892,B_1893] :
      ( r1_tarski(C_1891,k2_zfmisc_1(A_1892,B_1893))
      | ~ r2_hidden(C_1891,k1_funct_2(A_1892,B_1893)) ) ),
    inference(resolution,[status(thm)],[c_9003,c_12])).

tff(c_9028,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8576,c_9008])).

tff(c_8560,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8544,c_10])).

tff(c_8602,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8567,c_8560])).

tff(c_8557,plain,(
    ! [A_19] :
      ( A_19 != '#skF_2'
      | k6_relat_1(A_19) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8544,c_8544,c_127])).

tff(c_8638,plain,(
    ! [A_19] :
      ( A_19 != '#skF_3'
      | k6_relat_1(A_19) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8567,c_8567,c_8557])).

tff(c_9406,plain,(
    ! [A_1920,B_1921] :
      ( r1_tarski(k1_relat_1(A_1920),k1_relat_1(B_1921))
      | ~ r1_tarski(A_1920,B_1921)
      | ~ v1_relat_1(B_1921)
      | ~ v1_relat_1(A_1920) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_9415,plain,(
    ! [A_18,B_1921] :
      ( r1_tarski(A_18,k1_relat_1(B_1921))
      | ~ r1_tarski(k6_relat_1(A_18),B_1921)
      | ~ v1_relat_1(B_1921)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_9406])).

tff(c_9434,plain,(
    ! [A_1924,B_1925] :
      ( r1_tarski(A_1924,k1_relat_1(B_1925))
      | ~ r1_tarski(k6_relat_1(A_1924),B_1925)
      | ~ v1_relat_1(B_1925) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_9415])).

tff(c_9445,plain,(
    ! [A_19,B_1925] :
      ( r1_tarski(A_19,k1_relat_1(B_1925))
      | ~ r1_tarski('#skF_3',B_1925)
      | ~ v1_relat_1(B_1925)
      | A_19 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8638,c_9434])).

tff(c_9455,plain,(
    ! [A_1926,B_1927] :
      ( r1_tarski(A_1926,k1_relat_1(B_1927))
      | ~ v1_relat_1(B_1927)
      | A_1926 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8602,c_9445])).

tff(c_9465,plain,(
    ! [A_1926,A_18] :
      ( r1_tarski(A_1926,A_18)
      | ~ v1_relat_1(k6_relat_1(A_18))
      | A_1926 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_9455])).

tff(c_9500,plain,(
    ! [A_18] : r1_tarski('#skF_3',A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_9465])).

tff(c_10590,plain,(
    ! [B_3221,A_3222,C_3223] :
      ( k1_relset_1(B_3221,A_3222,C_3223) = B_3221
      | ~ r1_tarski(k6_relat_1(B_3221),C_3223)
      | ~ m1_subset_1(C_3223,k1_zfmisc_1(k2_zfmisc_1(B_3221,A_3222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_11045,plain,(
    ! [B_3250,A_3251,A_3252] :
      ( k1_relset_1(B_3250,A_3251,A_3252) = B_3250
      | ~ r1_tarski(k6_relat_1(B_3250),A_3252)
      | ~ r1_tarski(A_3252,k2_zfmisc_1(B_3250,A_3251)) ) ),
    inference(resolution,[status(thm)],[c_14,c_10590])).

tff(c_11074,plain,(
    ! [A_19,A_3251,A_3252] :
      ( k1_relset_1(A_19,A_3251,A_3252) = A_19
      | ~ r1_tarski('#skF_3',A_3252)
      | ~ r1_tarski(A_3252,k2_zfmisc_1(A_19,A_3251))
      | A_19 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8638,c_11045])).

tff(c_11098,plain,(
    ! [A_3256,A_3257,A_3258] :
      ( k1_relset_1(A_3256,A_3257,A_3258) = A_3256
      | ~ r1_tarski(A_3258,k2_zfmisc_1(A_3256,A_3257))
      | A_3256 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9500,c_11074])).

tff(c_11146,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9028,c_11098])).

tff(c_9341,plain,(
    ! [A_1911,B_1912,C_1913] :
      ( k1_relset_1(A_1911,B_1912,C_1913) = k1_relat_1(C_1913)
      | ~ m1_subset_1(C_1913,k1_zfmisc_1(k2_zfmisc_1(A_1911,B_1912))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_9351,plain,(
    ! [A_1914,B_1915,C_1916] :
      ( k1_relset_1(A_1914,B_1915,C_1916) = k1_relat_1(C_1916)
      | ~ r2_hidden(C_1916,k1_funct_2(A_1914,B_1915)) ) ),
    inference(resolution,[status(thm)],[c_62,c_9341])).

tff(c_9380,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8576,c_9351])).

tff(c_11147,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11146,c_9380])).

tff(c_11149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8574,c_11147])).

tff(c_11151,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_76,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_11171,plain,(
    ! [A_3259] :
      ( k1_relat_1(A_3259) != k1_xboole_0
      | k1_xboole_0 = A_3259
      | ~ v1_relat_1(A_3259) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_11183,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_76,c_11171])).

tff(c_11190,plain,
    ( k1_xboole_0 != '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11151,c_11183])).

tff(c_11191,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_11190])).

tff(c_11262,plain,(
    ! [A_3269,B_3270] :
      ( v1_xboole_0(k1_funct_2(A_3269,B_3270))
      | ~ v1_xboole_0(B_3270)
      | v1_xboole_0(A_3269) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_11269,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_11262,c_109])).

tff(c_11271,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_11269])).

tff(c_11462,plain,(
    ! [C_3299,A_3300,B_3301] :
      ( m1_subset_1(C_3299,k1_zfmisc_1(k2_zfmisc_1(A_3300,B_3301)))
      | ~ r2_hidden(C_3299,k1_funct_2(A_3300,B_3301)) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_11467,plain,(
    ! [C_3302,A_3303,B_3304] :
      ( r1_tarski(C_3302,k2_zfmisc_1(A_3303,B_3304))
      | ~ r2_hidden(C_3302,k1_funct_2(A_3303,B_3304)) ) ),
    inference(resolution,[status(thm)],[c_11462,c_12])).

tff(c_11485,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_11467])).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( k1_relat_1(k2_zfmisc_1(A_11,B_12)) = A_11
      | k1_xboole_0 = B_12
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12249,plain,(
    ! [A_3343,B_3344] :
      ( r1_tarski(k1_relat_1(A_3343),k1_relat_1(B_3344))
      | ~ r1_tarski(A_3343,B_3344)
      | ~ v1_relat_1(B_3344)
      | ~ v1_relat_1(A_3343) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12258,plain,(
    ! [B_3344] :
      ( r1_tarski('#skF_2',k1_relat_1(B_3344))
      | ~ r1_tarski('#skF_4',B_3344)
      | ~ v1_relat_1(B_3344)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11151,c_12249])).

tff(c_12280,plain,(
    ! [B_3345] :
      ( r1_tarski('#skF_2',k1_relat_1(B_3345))
      | ~ r1_tarski('#skF_4',B_3345)
      | ~ v1_relat_1(B_3345) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_12258])).

tff(c_12283,plain,(
    ! [A_11,B_12] :
      ( r1_tarski('#skF_2',A_11)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_11,B_12))
      | ~ v1_relat_1(k2_zfmisc_1(A_11,B_12))
      | k1_xboole_0 = B_12
      | k1_xboole_0 = A_11 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_12280])).

tff(c_12749,plain,(
    ! [A_3392,B_3393] :
      ( r1_tarski('#skF_2',A_3392)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_3392,B_3393))
      | k1_xboole_0 = B_3393
      | k1_xboole_0 = A_3392 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12283])).

tff(c_12774,plain,
    ( r1_tarski('#skF_2','#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_11485,c_12749])).

tff(c_12786,plain,
    ( r1_tarski('#skF_2','#skF_2')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_11191,c_12774])).

tff(c_12787,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_12786])).

tff(c_12851,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12787,c_6])).

tff(c_12853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11271,c_12851])).

tff(c_12855,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12786])).

tff(c_11150,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k2_relat_1(k2_zfmisc_1(A_11,B_12)) = B_12
      | k1_xboole_0 = B_12
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12076,plain,(
    ! [A_3326,B_3327] :
      ( r1_tarski(k2_relat_1(A_3326),k2_relat_1(B_3327))
      | ~ r1_tarski(A_3326,B_3327)
      | ~ v1_relat_1(B_3327)
      | ~ v1_relat_1(A_3326) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12088,plain,(
    ! [A_3326,B_12,A_11] :
      ( r1_tarski(k2_relat_1(A_3326),B_12)
      | ~ r1_tarski(A_3326,k2_zfmisc_1(A_11,B_12))
      | ~ v1_relat_1(k2_zfmisc_1(A_11,B_12))
      | ~ v1_relat_1(A_3326)
      | k1_xboole_0 = B_12
      | k1_xboole_0 = A_11 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_12076])).

tff(c_16097,plain,(
    ! [A_3577,B_3578,A_3579] :
      ( r1_tarski(k2_relat_1(A_3577),B_3578)
      | ~ r1_tarski(A_3577,k2_zfmisc_1(A_3579,B_3578))
      | ~ v1_relat_1(A_3577)
      | k1_xboole_0 = B_3578
      | k1_xboole_0 = A_3579 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12088])).

tff(c_16139,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_11485,c_16097])).

tff(c_16167,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_16139])).

tff(c_16169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11191,c_12855,c_11150,c_16167])).

tff(c_16170,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_11269])).

tff(c_16174,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_16170,c_8])).

tff(c_16178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11191,c_16174])).

tff(c_16179,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11190])).

tff(c_131,plain,(
    ! [A_50] :
      ( k1_xboole_0 != A_50
      | k6_relat_1(A_50) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_121])).

tff(c_137,plain,(
    ! [A_50] :
      ( k2_relat_1(k1_xboole_0) = A_50
      | k1_xboole_0 != A_50 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_36])).

tff(c_16259,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16179,c_16179,c_137])).

tff(c_128,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_76,c_115])).

tff(c_11170,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_16181,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16179,c_11170])).

tff(c_16263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16259,c_16181])).

tff(c_16264,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_16271,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16264,c_10])).

tff(c_16265,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_16279,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16264,c_16265])).

tff(c_16280,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16279,c_11150])).

tff(c_16304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16271,c_16280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.27/4.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.35/4.06  
% 10.35/4.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.35/4.06  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 10.35/4.06  
% 10.35/4.06  %Foreground sorts:
% 10.35/4.06  
% 10.35/4.06  
% 10.35/4.06  %Background operators:
% 10.35/4.06  
% 10.35/4.06  
% 10.35/4.06  %Foreground operators:
% 10.35/4.06  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.35/4.06  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 10.35/4.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.35/4.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.35/4.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.35/4.06  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.35/4.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.35/4.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.35/4.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.35/4.06  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.35/4.06  tff('#skF_2', type, '#skF_2': $i).
% 10.35/4.06  tff('#skF_3', type, '#skF_3': $i).
% 10.35/4.06  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.35/4.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.35/4.06  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 10.35/4.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.35/4.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.35/4.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.35/4.06  tff('#skF_4', type, '#skF_4': $i).
% 10.35/4.06  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.35/4.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.35/4.06  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 10.35/4.06  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.35/4.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.35/4.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.35/4.06  
% 10.43/4.08  tff(f_126, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_2)).
% 10.43/4.08  tff(f_147, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_2)).
% 10.43/4.08  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.43/4.08  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.43/4.08  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.43/4.08  tff(f_134, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 10.43/4.08  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.43/4.08  tff(f_89, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 10.43/4.08  tff(f_85, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 10.43/4.08  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.43/4.08  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 10.43/4.08  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 10.43/4.08  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relset_1)).
% 10.43/4.08  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.43/4.08  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 10.43/4.08  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.43/4.08  tff(f_56, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 10.43/4.08  tff(c_225, plain, (![A_59, B_60]: (v1_xboole_0(k1_funct_2(A_59, B_60)) | ~v1_xboole_0(B_60) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_126])).
% 10.43/4.08  tff(c_72, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 10.43/4.08  tff(c_105, plain, (![B_44, A_45]: (~r2_hidden(B_44, A_45) | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.43/4.08  tff(c_109, plain, (~v1_xboole_0(k1_funct_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_105])).
% 10.43/4.08  tff(c_232, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_225, c_109])).
% 10.43/4.08  tff(c_255, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_232])).
% 10.43/4.08  tff(c_70, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_147])).
% 10.43/4.08  tff(c_159, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_70])).
% 10.43/4.08  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.43/4.08  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.43/4.08  tff(c_287, plain, (![A_66, B_67]: (k1_funct_2(A_66, B_67)=k1_xboole_0 | ~v1_xboole_0(B_67) | v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_225, c_8])).
% 10.43/4.08  tff(c_294, plain, (![A_68]: (k1_funct_2(A_68, k1_xboole_0)=k1_xboole_0 | v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_6, c_287])).
% 10.43/4.08  tff(c_307, plain, (k1_funct_2('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_294, c_255])).
% 10.43/4.08  tff(c_459, plain, (![C_89, A_90, B_91]: (m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~r2_hidden(C_89, k1_funct_2(A_90, B_91)))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.43/4.08  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.43/4.08  tff(c_472, plain, (![C_94, A_95, B_96]: (r1_tarski(C_94, k2_zfmisc_1(A_95, B_96)) | ~r2_hidden(C_94, k1_funct_2(A_95, B_96)))), inference(resolution, [status(thm)], [c_459, c_12])).
% 10.43/4.08  tff(c_481, plain, (![C_94]: (r1_tarski(C_94, k2_zfmisc_1('#skF_3', k1_xboole_0)) | ~r2_hidden(C_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_307, c_472])).
% 10.43/4.08  tff(c_38, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.43/4.08  tff(c_34, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.43/4.08  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.43/4.08  tff(c_36, plain, (![A_18]: (k2_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.43/4.08  tff(c_115, plain, (![A_47]: (k2_relat_1(A_47)!=k1_xboole_0 | k1_xboole_0=A_47 | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.43/4.08  tff(c_121, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))!=k1_xboole_0 | k6_relat_1(A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_115])).
% 10.43/4.08  tff(c_127, plain, (![A_19]: (k1_xboole_0!=A_19 | k6_relat_1(A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_121])).
% 10.43/4.08  tff(c_1163, plain, (![A_129, B_130]: (r1_tarski(k1_relat_1(A_129), k1_relat_1(B_130)) | ~r1_tarski(A_129, B_130) | ~v1_relat_1(B_130) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.43/4.08  tff(c_1172, plain, (![A_18, B_130]: (r1_tarski(A_18, k1_relat_1(B_130)) | ~r1_tarski(k6_relat_1(A_18), B_130) | ~v1_relat_1(B_130) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1163])).
% 10.43/4.08  tff(c_1184, plain, (![A_131, B_132]: (r1_tarski(A_131, k1_relat_1(B_132)) | ~r1_tarski(k6_relat_1(A_131), B_132) | ~v1_relat_1(B_132))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1172])).
% 10.43/4.08  tff(c_1199, plain, (![A_19, B_132]: (r1_tarski(A_19, k1_relat_1(B_132)) | ~r1_tarski(k1_xboole_0, B_132) | ~v1_relat_1(B_132) | k1_xboole_0!=A_19)), inference(superposition, [status(thm), theory('equality')], [c_127, c_1184])).
% 10.43/4.08  tff(c_1212, plain, (![A_133, B_134]: (r1_tarski(A_133, k1_relat_1(B_134)) | ~v1_relat_1(B_134) | k1_xboole_0!=A_133)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1199])).
% 10.43/4.08  tff(c_1222, plain, (![A_133, A_18]: (r1_tarski(A_133, A_18) | ~v1_relat_1(k6_relat_1(A_18)) | k1_xboole_0!=A_133)), inference(superposition, [status(thm), theory('equality')], [c_34, c_1212])).
% 10.43/4.08  tff(c_1228, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1222])).
% 10.43/4.08  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.43/4.08  tff(c_1923, plain, (![B_194, A_195, C_196]: (k1_relset_1(B_194, A_195, C_196)=B_194 | ~r1_tarski(k6_relat_1(B_194), C_196) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(B_194, A_195))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.43/4.08  tff(c_3160, plain, (![B_1721, A_1722, A_1723]: (k1_relset_1(B_1721, A_1722, A_1723)=B_1721 | ~r1_tarski(k6_relat_1(B_1721), A_1723) | ~r1_tarski(A_1723, k2_zfmisc_1(B_1721, A_1722)))), inference(resolution, [status(thm)], [c_14, c_1923])).
% 10.43/4.08  tff(c_3207, plain, (![A_19, A_1722, A_1723]: (k1_relset_1(A_19, A_1722, A_1723)=A_19 | ~r1_tarski(k1_xboole_0, A_1723) | ~r1_tarski(A_1723, k2_zfmisc_1(A_19, A_1722)) | k1_xboole_0!=A_19)), inference(superposition, [status(thm), theory('equality')], [c_127, c_3160])).
% 10.43/4.08  tff(c_3353, plain, (![A_1728, A_1729, A_1730]: (k1_relset_1(A_1728, A_1729, A_1730)=A_1728 | ~r1_tarski(A_1730, k2_zfmisc_1(A_1728, A_1729)) | k1_xboole_0!=A_1728)), inference(demodulation, [status(thm), theory('equality')], [c_1228, c_3207])).
% 10.43/4.08  tff(c_3416, plain, (![C_94]: (k1_relset_1('#skF_3', k1_xboole_0, C_94)='#skF_3' | k1_xboole_0!='#skF_3' | ~r2_hidden(C_94, k1_xboole_0))), inference(resolution, [status(thm)], [c_481, c_3353])).
% 10.43/4.09  tff(c_3792, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_3416])).
% 10.43/4.09  tff(c_277, plain, (![C_63, A_64, B_65]: (v1_funct_2(C_63, A_64, B_65) | ~r2_hidden(C_63, k1_funct_2(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.43/4.09  tff(c_286, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_277])).
% 10.43/4.09  tff(c_62, plain, (![C_33, A_31, B_32]: (m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~r2_hidden(C_33, k1_funct_2(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.43/4.09  tff(c_594, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.43/4.09  tff(c_1000, plain, (![A_110, B_111, C_112]: (k1_relset_1(A_110, B_111, C_112)=k1_relat_1(C_112) | ~r2_hidden(C_112, k1_funct_2(A_110, B_111)))), inference(resolution, [status(thm)], [c_62, c_594])).
% 10.43/4.09  tff(c_1039, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_1000])).
% 10.43/4.09  tff(c_3012, plain, (![B_1707, A_1708, C_1709]: (k1_xboole_0=B_1707 | k1_relset_1(A_1708, B_1707, C_1709)=A_1708 | ~v1_funct_2(C_1709, A_1708, B_1707) | ~m1_subset_1(C_1709, k1_zfmisc_1(k2_zfmisc_1(A_1708, B_1707))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.43/4.09  tff(c_8324, plain, (![B_1849, A_1850, C_1851]: (k1_xboole_0=B_1849 | k1_relset_1(A_1850, B_1849, C_1851)=A_1850 | ~v1_funct_2(C_1851, A_1850, B_1849) | ~r2_hidden(C_1851, k1_funct_2(A_1850, B_1849)))), inference(resolution, [status(thm)], [c_62, c_3012])).
% 10.43/4.09  tff(c_8406, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_8324])).
% 10.43/4.09  tff(c_8419, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_286, c_1039, c_8406])).
% 10.43/4.09  tff(c_8421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_3792, c_8419])).
% 10.43/4.09  tff(c_8423, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3416])).
% 10.43/4.09  tff(c_8536, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8423, c_6])).
% 10.43/4.09  tff(c_8538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_255, c_8536])).
% 10.43/4.09  tff(c_8540, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_232])).
% 10.43/4.09  tff(c_8548, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8540, c_8])).
% 10.43/4.09  tff(c_8539, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_232])).
% 10.43/4.09  tff(c_8544, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8539, c_8])).
% 10.43/4.09  tff(c_8567, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8548, c_8544])).
% 10.43/4.09  tff(c_8574, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8567, c_159])).
% 10.43/4.09  tff(c_8576, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8567, c_72])).
% 10.43/4.09  tff(c_9003, plain, (![C_1888, A_1889, B_1890]: (m1_subset_1(C_1888, k1_zfmisc_1(k2_zfmisc_1(A_1889, B_1890))) | ~r2_hidden(C_1888, k1_funct_2(A_1889, B_1890)))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.43/4.09  tff(c_9008, plain, (![C_1891, A_1892, B_1893]: (r1_tarski(C_1891, k2_zfmisc_1(A_1892, B_1893)) | ~r2_hidden(C_1891, k1_funct_2(A_1892, B_1893)))), inference(resolution, [status(thm)], [c_9003, c_12])).
% 10.43/4.09  tff(c_9028, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_8576, c_9008])).
% 10.43/4.09  tff(c_8560, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_8544, c_10])).
% 10.43/4.09  tff(c_8602, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_8567, c_8560])).
% 10.43/4.09  tff(c_8557, plain, (![A_19]: (A_19!='#skF_2' | k6_relat_1(A_19)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8544, c_8544, c_127])).
% 10.43/4.09  tff(c_8638, plain, (![A_19]: (A_19!='#skF_3' | k6_relat_1(A_19)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8567, c_8567, c_8557])).
% 10.43/4.09  tff(c_9406, plain, (![A_1920, B_1921]: (r1_tarski(k1_relat_1(A_1920), k1_relat_1(B_1921)) | ~r1_tarski(A_1920, B_1921) | ~v1_relat_1(B_1921) | ~v1_relat_1(A_1920))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.43/4.09  tff(c_9415, plain, (![A_18, B_1921]: (r1_tarski(A_18, k1_relat_1(B_1921)) | ~r1_tarski(k6_relat_1(A_18), B_1921) | ~v1_relat_1(B_1921) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_9406])).
% 10.43/4.09  tff(c_9434, plain, (![A_1924, B_1925]: (r1_tarski(A_1924, k1_relat_1(B_1925)) | ~r1_tarski(k6_relat_1(A_1924), B_1925) | ~v1_relat_1(B_1925))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_9415])).
% 10.43/4.09  tff(c_9445, plain, (![A_19, B_1925]: (r1_tarski(A_19, k1_relat_1(B_1925)) | ~r1_tarski('#skF_3', B_1925) | ~v1_relat_1(B_1925) | A_19!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8638, c_9434])).
% 10.43/4.09  tff(c_9455, plain, (![A_1926, B_1927]: (r1_tarski(A_1926, k1_relat_1(B_1927)) | ~v1_relat_1(B_1927) | A_1926!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8602, c_9445])).
% 10.43/4.09  tff(c_9465, plain, (![A_1926, A_18]: (r1_tarski(A_1926, A_18) | ~v1_relat_1(k6_relat_1(A_18)) | A_1926!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_9455])).
% 10.43/4.09  tff(c_9500, plain, (![A_18]: (r1_tarski('#skF_3', A_18))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_9465])).
% 10.43/4.09  tff(c_10590, plain, (![B_3221, A_3222, C_3223]: (k1_relset_1(B_3221, A_3222, C_3223)=B_3221 | ~r1_tarski(k6_relat_1(B_3221), C_3223) | ~m1_subset_1(C_3223, k1_zfmisc_1(k2_zfmisc_1(B_3221, A_3222))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.43/4.09  tff(c_11045, plain, (![B_3250, A_3251, A_3252]: (k1_relset_1(B_3250, A_3251, A_3252)=B_3250 | ~r1_tarski(k6_relat_1(B_3250), A_3252) | ~r1_tarski(A_3252, k2_zfmisc_1(B_3250, A_3251)))), inference(resolution, [status(thm)], [c_14, c_10590])).
% 10.43/4.09  tff(c_11074, plain, (![A_19, A_3251, A_3252]: (k1_relset_1(A_19, A_3251, A_3252)=A_19 | ~r1_tarski('#skF_3', A_3252) | ~r1_tarski(A_3252, k2_zfmisc_1(A_19, A_3251)) | A_19!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8638, c_11045])).
% 10.43/4.09  tff(c_11098, plain, (![A_3256, A_3257, A_3258]: (k1_relset_1(A_3256, A_3257, A_3258)=A_3256 | ~r1_tarski(A_3258, k2_zfmisc_1(A_3256, A_3257)) | A_3256!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9500, c_11074])).
% 10.43/4.09  tff(c_11146, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_9028, c_11098])).
% 10.43/4.09  tff(c_9341, plain, (![A_1911, B_1912, C_1913]: (k1_relset_1(A_1911, B_1912, C_1913)=k1_relat_1(C_1913) | ~m1_subset_1(C_1913, k1_zfmisc_1(k2_zfmisc_1(A_1911, B_1912))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.43/4.09  tff(c_9351, plain, (![A_1914, B_1915, C_1916]: (k1_relset_1(A_1914, B_1915, C_1916)=k1_relat_1(C_1916) | ~r2_hidden(C_1916, k1_funct_2(A_1914, B_1915)))), inference(resolution, [status(thm)], [c_62, c_9341])).
% 10.43/4.09  tff(c_9380, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8576, c_9351])).
% 10.43/4.09  tff(c_11147, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11146, c_9380])).
% 10.43/4.09  tff(c_11149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8574, c_11147])).
% 10.43/4.09  tff(c_11151, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_70])).
% 10.43/4.09  tff(c_76, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 10.43/4.09  tff(c_11171, plain, (![A_3259]: (k1_relat_1(A_3259)!=k1_xboole_0 | k1_xboole_0=A_3259 | ~v1_relat_1(A_3259))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.43/4.09  tff(c_11183, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_76, c_11171])).
% 10.43/4.09  tff(c_11190, plain, (k1_xboole_0!='#skF_2' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11151, c_11183])).
% 10.43/4.09  tff(c_11191, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_11190])).
% 10.43/4.09  tff(c_11262, plain, (![A_3269, B_3270]: (v1_xboole_0(k1_funct_2(A_3269, B_3270)) | ~v1_xboole_0(B_3270) | v1_xboole_0(A_3269))), inference(cnfTransformation, [status(thm)], [f_126])).
% 10.43/4.09  tff(c_11269, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_11262, c_109])).
% 10.43/4.09  tff(c_11271, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_11269])).
% 10.43/4.09  tff(c_11462, plain, (![C_3299, A_3300, B_3301]: (m1_subset_1(C_3299, k1_zfmisc_1(k2_zfmisc_1(A_3300, B_3301))) | ~r2_hidden(C_3299, k1_funct_2(A_3300, B_3301)))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.43/4.09  tff(c_11467, plain, (![C_3302, A_3303, B_3304]: (r1_tarski(C_3302, k2_zfmisc_1(A_3303, B_3304)) | ~r2_hidden(C_3302, k1_funct_2(A_3303, B_3304)))), inference(resolution, [status(thm)], [c_11462, c_12])).
% 10.43/4.09  tff(c_11485, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_11467])).
% 10.43/4.09  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.43/4.09  tff(c_20, plain, (![A_11, B_12]: (k1_relat_1(k2_zfmisc_1(A_11, B_12))=A_11 | k1_xboole_0=B_12 | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.43/4.09  tff(c_12249, plain, (![A_3343, B_3344]: (r1_tarski(k1_relat_1(A_3343), k1_relat_1(B_3344)) | ~r1_tarski(A_3343, B_3344) | ~v1_relat_1(B_3344) | ~v1_relat_1(A_3343))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.43/4.09  tff(c_12258, plain, (![B_3344]: (r1_tarski('#skF_2', k1_relat_1(B_3344)) | ~r1_tarski('#skF_4', B_3344) | ~v1_relat_1(B_3344) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11151, c_12249])).
% 10.43/4.09  tff(c_12280, plain, (![B_3345]: (r1_tarski('#skF_2', k1_relat_1(B_3345)) | ~r1_tarski('#skF_4', B_3345) | ~v1_relat_1(B_3345))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_12258])).
% 10.43/4.09  tff(c_12283, plain, (![A_11, B_12]: (r1_tarski('#skF_2', A_11) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_11, B_12)) | ~v1_relat_1(k2_zfmisc_1(A_11, B_12)) | k1_xboole_0=B_12 | k1_xboole_0=A_11)), inference(superposition, [status(thm), theory('equality')], [c_20, c_12280])).
% 10.43/4.09  tff(c_12749, plain, (![A_3392, B_3393]: (r1_tarski('#skF_2', A_3392) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_3392, B_3393)) | k1_xboole_0=B_3393 | k1_xboole_0=A_3392)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_12283])).
% 10.43/4.09  tff(c_12774, plain, (r1_tarski('#skF_2', '#skF_2') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_11485, c_12749])).
% 10.43/4.09  tff(c_12786, plain, (r1_tarski('#skF_2', '#skF_2') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_11191, c_12774])).
% 10.43/4.09  tff(c_12787, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_12786])).
% 10.43/4.09  tff(c_12851, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12787, c_6])).
% 10.43/4.09  tff(c_12853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11271, c_12851])).
% 10.43/4.09  tff(c_12855, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_12786])).
% 10.43/4.09  tff(c_11150, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_70])).
% 10.43/4.09  tff(c_18, plain, (![A_11, B_12]: (k2_relat_1(k2_zfmisc_1(A_11, B_12))=B_12 | k1_xboole_0=B_12 | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.43/4.09  tff(c_12076, plain, (![A_3326, B_3327]: (r1_tarski(k2_relat_1(A_3326), k2_relat_1(B_3327)) | ~r1_tarski(A_3326, B_3327) | ~v1_relat_1(B_3327) | ~v1_relat_1(A_3326))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.43/4.09  tff(c_12088, plain, (![A_3326, B_12, A_11]: (r1_tarski(k2_relat_1(A_3326), B_12) | ~r1_tarski(A_3326, k2_zfmisc_1(A_11, B_12)) | ~v1_relat_1(k2_zfmisc_1(A_11, B_12)) | ~v1_relat_1(A_3326) | k1_xboole_0=B_12 | k1_xboole_0=A_11)), inference(superposition, [status(thm), theory('equality')], [c_18, c_12076])).
% 10.43/4.09  tff(c_16097, plain, (![A_3577, B_3578, A_3579]: (r1_tarski(k2_relat_1(A_3577), B_3578) | ~r1_tarski(A_3577, k2_zfmisc_1(A_3579, B_3578)) | ~v1_relat_1(A_3577) | k1_xboole_0=B_3578 | k1_xboole_0=A_3579)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_12088])).
% 10.43/4.09  tff(c_16139, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_11485, c_16097])).
% 10.43/4.09  tff(c_16167, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_16139])).
% 10.43/4.09  tff(c_16169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11191, c_12855, c_11150, c_16167])).
% 10.43/4.09  tff(c_16170, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_11269])).
% 10.43/4.09  tff(c_16174, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_16170, c_8])).
% 10.43/4.09  tff(c_16178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11191, c_16174])).
% 10.43/4.09  tff(c_16179, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_11190])).
% 10.43/4.09  tff(c_131, plain, (![A_50]: (k1_xboole_0!=A_50 | k6_relat_1(A_50)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_121])).
% 10.43/4.09  tff(c_137, plain, (![A_50]: (k2_relat_1(k1_xboole_0)=A_50 | k1_xboole_0!=A_50)), inference(superposition, [status(thm), theory('equality')], [c_131, c_36])).
% 10.43/4.09  tff(c_16259, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16179, c_16179, c_137])).
% 10.43/4.09  tff(c_128, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_76, c_115])).
% 10.43/4.09  tff(c_11170, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_128])).
% 10.43/4.09  tff(c_16181, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16179, c_11170])).
% 10.43/4.09  tff(c_16263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16259, c_16181])).
% 10.43/4.09  tff(c_16264, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_128])).
% 10.43/4.09  tff(c_16271, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_16264, c_10])).
% 10.43/4.09  tff(c_16265, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_128])).
% 10.43/4.09  tff(c_16279, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16264, c_16265])).
% 10.43/4.09  tff(c_16280, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16279, c_11150])).
% 10.43/4.09  tff(c_16304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16271, c_16280])).
% 10.43/4.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.43/4.09  
% 10.43/4.09  Inference rules
% 10.43/4.09  ----------------------
% 10.43/4.09  #Ref     : 14
% 10.43/4.09  #Sup     : 3549
% 10.43/4.09  #Fact    : 14
% 10.43/4.09  #Define  : 0
% 10.43/4.09  #Split   : 38
% 10.43/4.09  #Chain   : 0
% 10.43/4.09  #Close   : 0
% 10.43/4.09  
% 10.43/4.09  Ordering : KBO
% 10.43/4.09  
% 10.43/4.09  Simplification rules
% 10.43/4.09  ----------------------
% 10.43/4.09  #Subsume      : 927
% 10.43/4.09  #Demod        : 1288
% 10.43/4.09  #Tautology    : 1226
% 10.43/4.09  #SimpNegUnit  : 188
% 10.43/4.09  #BackRed      : 222
% 10.43/4.09  
% 10.43/4.09  #Partial instantiations: 259
% 10.43/4.09  #Strategies tried      : 1
% 10.43/4.09  
% 10.43/4.09  Timing (in seconds)
% 10.43/4.09  ----------------------
% 10.43/4.09  Preprocessing        : 0.54
% 10.43/4.09  Parsing              : 0.28
% 10.43/4.09  CNF conversion       : 0.04
% 10.43/4.09  Main loop            : 2.61
% 10.43/4.09  Inferencing          : 0.81
% 10.43/4.09  Reduction            : 0.73
% 10.43/4.09  Demodulation         : 0.49
% 10.43/4.09  BG Simplification    : 0.09
% 10.43/4.09  Subsumption          : 0.79
% 10.43/4.09  Abstraction          : 0.10
% 10.43/4.09  MUC search           : 0.00
% 10.43/4.09  Cooper               : 0.00
% 10.43/4.09  Total                : 3.22
% 10.43/4.09  Index Insertion      : 0.00
% 10.43/4.09  Index Deletion       : 0.00
% 10.43/4.09  Index Matching       : 0.00
% 10.43/4.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
