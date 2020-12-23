%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:45 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 581 expanded)
%              Number of leaves         :   29 ( 200 expanded)
%              Depth                    :   14
%              Number of atoms          :  187 (1454 expanded)
%              Number of equality atoms :   55 ( 422 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_86,axiom,(
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

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_9796,plain,(
    ! [A_485] :
      ( r1_tarski(A_485,k2_zfmisc_1(k1_relat_1(A_485),k2_relat_1(A_485)))
      | ~ v1_relat_1(A_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_114,plain,(
    ! [C_40,B_41,A_42] :
      ( ~ v1_xboole_0(C_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(C_40))
      | ~ r2_hidden(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_122,plain,(
    ! [B_44,A_45,A_46] :
      ( ~ v1_xboole_0(B_44)
      | ~ r2_hidden(A_45,A_46)
      | ~ r1_tarski(A_46,B_44) ) ),
    inference(resolution,[status(thm)],[c_24,c_114])).

tff(c_126,plain,(
    ! [B_47,A_48,B_49] :
      ( ~ v1_xboole_0(B_47)
      | ~ r1_tarski(A_48,B_47)
      | r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_6,c_122])).

tff(c_132,plain,(
    ! [B_7,B_49] :
      ( ~ v1_xboole_0(B_7)
      | r1_tarski(B_7,B_49) ) ),
    inference(resolution,[status(thm)],[c_14,c_126])).

tff(c_429,plain,(
    ! [B_87,C_88,A_89] :
      ( k1_xboole_0 = B_87
      | v1_funct_2(C_88,A_89,B_87)
      | k1_relset_1(A_89,B_87,C_88) != A_89
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1933,plain,(
    ! [B_208,A_209,A_210] :
      ( k1_xboole_0 = B_208
      | v1_funct_2(A_209,A_210,B_208)
      | k1_relset_1(A_210,B_208,A_209) != A_210
      | ~ r1_tarski(A_209,k2_zfmisc_1(A_210,B_208)) ) ),
    inference(resolution,[status(thm)],[c_24,c_429])).

tff(c_3775,plain,(
    ! [B_310,B_311,A_312] :
      ( k1_xboole_0 = B_310
      | v1_funct_2(B_311,A_312,B_310)
      | k1_relset_1(A_312,B_310,B_311) != A_312
      | ~ v1_xboole_0(B_311) ) ),
    inference(resolution,[status(thm)],[c_132,c_1933])).

tff(c_48,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_88,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_3800,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_3775,c_88])).

tff(c_3801,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3800])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    ! [A_22] :
      ( v1_funct_2(k1_xboole_0,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_22,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_55,plain,(
    ! [A_22] :
      ( v1_funct_2(k1_xboole_0,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_34])).

tff(c_168,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_171,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_168])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_171])).

tff(c_177,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_26,plain,(
    ! [C_14,B_13,A_12] :
      ( ~ v1_xboole_0(C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_179,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_177,c_26])).

tff(c_188,plain,(
    ! [A_60] : ~ r2_hidden(A_60,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_179])).

tff(c_193,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_188])).

tff(c_28,plain,(
    ! [A_15] :
      ( r1_tarski(A_15,k2_zfmisc_1(k1_relat_1(A_15),k2_relat_1(A_15)))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_224,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_632,plain,(
    ! [A_110,B_111,A_112] :
      ( k1_relset_1(A_110,B_111,A_112) = k1_relat_1(A_112)
      | ~ r1_tarski(A_112,k2_zfmisc_1(A_110,B_111)) ) ),
    inference(resolution,[status(thm)],[c_24,c_224])).

tff(c_657,plain,(
    ! [A_15] :
      ( k1_relset_1(k1_relat_1(A_15),k2_relat_1(A_15),A_15) = k1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_28,c_632])).

tff(c_9100,plain,(
    ! [A_469] :
      ( k2_relat_1(A_469) = k1_xboole_0
      | v1_funct_2(A_469,k1_relat_1(A_469),k2_relat_1(A_469))
      | k1_relset_1(k1_relat_1(A_469),k2_relat_1(A_469),A_469) != k1_relat_1(A_469)
      | ~ v1_relat_1(A_469) ) ),
    inference(resolution,[status(thm)],[c_28,c_1933])).

tff(c_9110,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_9100,c_88])).

tff(c_9165,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_9110])).

tff(c_9168,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_9165])).

tff(c_9174,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_9168])).

tff(c_9180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_9174])).

tff(c_9181,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_9165])).

tff(c_118,plain,(
    ! [A_43] :
      ( r1_tarski(A_43,k2_zfmisc_1(k1_relat_1(A_43),k2_relat_1(A_43)))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_121,plain,(
    ! [A_43] :
      ( k2_zfmisc_1(k1_relat_1(A_43),k2_relat_1(A_43)) = A_43
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_43),k2_relat_1(A_43)),A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_118,c_10])).

tff(c_9200,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'),k1_xboole_0),'#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9181,c_121])).

tff(c_9222,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_193,c_18,c_18,c_9181,c_9200])).

tff(c_9335,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9222,c_8])).

tff(c_9337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3801,c_9335])).

tff(c_9339,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3800])).

tff(c_133,plain,(
    ! [B_50,B_51] :
      ( ~ v1_xboole_0(B_50)
      | r1_tarski(B_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_14,c_126])).

tff(c_144,plain,(
    ! [B_56,B_55] :
      ( B_56 = B_55
      | ~ r1_tarski(B_55,B_56)
      | ~ v1_xboole_0(B_56) ) ),
    inference(resolution,[status(thm)],[c_133,c_10])).

tff(c_158,plain,(
    ! [B_58,B_57] :
      ( B_58 = B_57
      | ~ v1_xboole_0(B_58)
      | ~ v1_xboole_0(B_57) ) ),
    inference(resolution,[status(thm)],[c_132,c_144])).

tff(c_161,plain,(
    ! [B_57] :
      ( k1_xboole_0 = B_57
      | ~ v1_xboole_0(B_57) ) ),
    inference(resolution,[status(thm)],[c_8,c_158])).

tff(c_9384,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_9339,c_161])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_279,plain,(
    ! [B_76,C_77] :
      ( k1_relset_1(k1_xboole_0,B_76,C_77) = k1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_224])).

tff(c_285,plain,(
    ! [B_76] : k1_relset_1(k1_xboole_0,B_76,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_177,c_279])).

tff(c_317,plain,(
    ! [A_81,B_82,C_83] :
      ( m1_subset_1(k1_relset_1(A_81,B_82,C_83),k1_zfmisc_1(A_81))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_335,plain,(
    ! [B_76] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_76))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_317])).

tff(c_347,plain,(
    m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_20,c_335])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_364,plain,(
    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_347,c_22])).

tff(c_194,plain,(
    ! [B_61] : r1_tarski(k1_xboole_0,B_61) ),
    inference(resolution,[status(thm)],[c_6,c_188])).

tff(c_205,plain,(
    ! [B_61] :
      ( k1_xboole_0 = B_61
      | ~ r1_tarski(B_61,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_194,c_10])).

tff(c_387,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_364,c_205])).

tff(c_237,plain,(
    ! [A_67,C_68] :
      ( k1_relset_1(A_67,k1_xboole_0,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_224])).

tff(c_243,plain,(
    ! [A_67] : k1_relset_1(A_67,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_177,c_237])).

tff(c_338,plain,(
    ! [A_67] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_67))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_67,k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_317])).

tff(c_349,plain,(
    ! [A_67] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_67)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_18,c_338])).

tff(c_449,plain,(
    ! [A_90] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_90)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_349])).

tff(c_32,plain,(
    ! [A_19,B_20,C_21] :
      ( k1_relset_1(A_19,B_20,C_21) = k1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_466,plain,(
    ! [A_19,B_20] : k1_relset_1(A_19,B_20,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_449,c_32])).

tff(c_479,plain,(
    ! [A_19,B_20] : k1_relset_1(A_19,B_20,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_466])).

tff(c_38,plain,(
    ! [C_24,B_23] :
      ( v1_funct_2(C_24,k1_xboole_0,B_23)
      | k1_relset_1(k1_xboole_0,B_23,C_24) != k1_xboole_0
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_413,plain,(
    ! [C_85,B_86] :
      ( v1_funct_2(C_85,k1_xboole_0,B_86)
      | k1_relset_1(k1_xboole_0,B_86,C_85) != k1_xboole_0
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_38])).

tff(c_424,plain,(
    ! [B_86] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_86)
      | k1_relset_1(k1_xboole_0,B_86,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_177,c_413])).

tff(c_579,plain,(
    ! [B_86] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_424])).

tff(c_9423,plain,(
    ! [B_86] : v1_funct_2('#skF_2','#skF_2',B_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9384,c_9384,c_579])).

tff(c_9430,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9384,c_9384,c_387])).

tff(c_9450,plain,(
    ~ v1_funct_2('#skF_2','#skF_2',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9430,c_88])).

tff(c_9764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9423,c_9450])).

tff(c_9765,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_9777,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_24,c_9765])).

tff(c_9801,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_9796,c_9777])).

tff(c_9806,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_9801])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.80/2.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/2.66  
% 7.80/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/2.66  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.80/2.66  
% 7.80/2.66  %Foreground sorts:
% 7.80/2.66  
% 7.80/2.66  
% 7.80/2.66  %Background operators:
% 7.80/2.66  
% 7.80/2.66  
% 7.80/2.66  %Foreground operators:
% 7.80/2.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.80/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.80/2.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.80/2.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.80/2.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.80/2.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.80/2.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.80/2.66  tff('#skF_2', type, '#skF_2': $i).
% 7.80/2.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.80/2.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.80/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.80/2.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.80/2.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.80/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.80/2.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.80/2.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.80/2.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.80/2.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.80/2.66  
% 7.80/2.68  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 7.80/2.68  tff(f_60, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 7.80/2.68  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.80/2.68  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.80/2.68  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.80/2.68  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 7.80/2.68  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.80/2.68  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.80/2.68  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.80/2.68  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.80/2.68  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 7.80/2.68  tff(c_50, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.80/2.68  tff(c_9796, plain, (![A_485]: (r1_tarski(A_485, k2_zfmisc_1(k1_relat_1(A_485), k2_relat_1(A_485))) | ~v1_relat_1(A_485))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.80/2.68  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.80/2.68  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.80/2.68  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.80/2.68  tff(c_114, plain, (![C_40, B_41, A_42]: (~v1_xboole_0(C_40) | ~m1_subset_1(B_41, k1_zfmisc_1(C_40)) | ~r2_hidden(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.80/2.68  tff(c_122, plain, (![B_44, A_45, A_46]: (~v1_xboole_0(B_44) | ~r2_hidden(A_45, A_46) | ~r1_tarski(A_46, B_44))), inference(resolution, [status(thm)], [c_24, c_114])).
% 7.80/2.68  tff(c_126, plain, (![B_47, A_48, B_49]: (~v1_xboole_0(B_47) | ~r1_tarski(A_48, B_47) | r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_6, c_122])).
% 7.80/2.68  tff(c_132, plain, (![B_7, B_49]: (~v1_xboole_0(B_7) | r1_tarski(B_7, B_49))), inference(resolution, [status(thm)], [c_14, c_126])).
% 7.80/2.68  tff(c_429, plain, (![B_87, C_88, A_89]: (k1_xboole_0=B_87 | v1_funct_2(C_88, A_89, B_87) | k1_relset_1(A_89, B_87, C_88)!=A_89 | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_87))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.80/2.68  tff(c_1933, plain, (![B_208, A_209, A_210]: (k1_xboole_0=B_208 | v1_funct_2(A_209, A_210, B_208) | k1_relset_1(A_210, B_208, A_209)!=A_210 | ~r1_tarski(A_209, k2_zfmisc_1(A_210, B_208)))), inference(resolution, [status(thm)], [c_24, c_429])).
% 7.80/2.68  tff(c_3775, plain, (![B_310, B_311, A_312]: (k1_xboole_0=B_310 | v1_funct_2(B_311, A_312, B_310) | k1_relset_1(A_312, B_310, B_311)!=A_312 | ~v1_xboole_0(B_311))), inference(resolution, [status(thm)], [c_132, c_1933])).
% 7.80/2.68  tff(c_48, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.80/2.68  tff(c_46, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.80/2.68  tff(c_52, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 7.80/2.68  tff(c_88, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_52])).
% 7.80/2.68  tff(c_3800, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_3775, c_88])).
% 7.80/2.68  tff(c_3801, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3800])).
% 7.80/2.68  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.80/2.68  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.80/2.68  tff(c_34, plain, (![A_22]: (v1_funct_2(k1_xboole_0, A_22, k1_xboole_0) | k1_xboole_0=A_22 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_22, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.80/2.68  tff(c_55, plain, (![A_22]: (v1_funct_2(k1_xboole_0, A_22, k1_xboole_0) | k1_xboole_0=A_22 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_34])).
% 7.80/2.68  tff(c_168, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_55])).
% 7.80/2.68  tff(c_171, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_168])).
% 7.80/2.68  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_171])).
% 7.80/2.68  tff(c_177, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_55])).
% 7.80/2.68  tff(c_26, plain, (![C_14, B_13, A_12]: (~v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.80/2.68  tff(c_179, plain, (![A_12]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_177, c_26])).
% 7.80/2.68  tff(c_188, plain, (![A_60]: (~r2_hidden(A_60, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_179])).
% 7.80/2.68  tff(c_193, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_188])).
% 7.80/2.68  tff(c_28, plain, (![A_15]: (r1_tarski(A_15, k2_zfmisc_1(k1_relat_1(A_15), k2_relat_1(A_15))) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.80/2.68  tff(c_224, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.80/2.68  tff(c_632, plain, (![A_110, B_111, A_112]: (k1_relset_1(A_110, B_111, A_112)=k1_relat_1(A_112) | ~r1_tarski(A_112, k2_zfmisc_1(A_110, B_111)))), inference(resolution, [status(thm)], [c_24, c_224])).
% 7.80/2.68  tff(c_657, plain, (![A_15]: (k1_relset_1(k1_relat_1(A_15), k2_relat_1(A_15), A_15)=k1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(resolution, [status(thm)], [c_28, c_632])).
% 7.80/2.68  tff(c_9100, plain, (![A_469]: (k2_relat_1(A_469)=k1_xboole_0 | v1_funct_2(A_469, k1_relat_1(A_469), k2_relat_1(A_469)) | k1_relset_1(k1_relat_1(A_469), k2_relat_1(A_469), A_469)!=k1_relat_1(A_469) | ~v1_relat_1(A_469))), inference(resolution, [status(thm)], [c_28, c_1933])).
% 7.80/2.68  tff(c_9110, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_9100, c_88])).
% 7.80/2.68  tff(c_9165, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_9110])).
% 7.80/2.68  tff(c_9168, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_9165])).
% 7.80/2.68  tff(c_9174, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_657, c_9168])).
% 7.80/2.68  tff(c_9180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_9174])).
% 7.80/2.68  tff(c_9181, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_9165])).
% 7.80/2.68  tff(c_118, plain, (![A_43]: (r1_tarski(A_43, k2_zfmisc_1(k1_relat_1(A_43), k2_relat_1(A_43))) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.80/2.68  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.80/2.68  tff(c_121, plain, (![A_43]: (k2_zfmisc_1(k1_relat_1(A_43), k2_relat_1(A_43))=A_43 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_43), k2_relat_1(A_43)), A_43) | ~v1_relat_1(A_43))), inference(resolution, [status(thm)], [c_118, c_10])).
% 7.80/2.68  tff(c_9200, plain, (k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))='#skF_2' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'), k1_xboole_0), '#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9181, c_121])).
% 7.80/2.68  tff(c_9222, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_193, c_18, c_18, c_9181, c_9200])).
% 7.80/2.68  tff(c_9335, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9222, c_8])).
% 7.80/2.68  tff(c_9337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3801, c_9335])).
% 7.80/2.68  tff(c_9339, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_3800])).
% 7.80/2.68  tff(c_133, plain, (![B_50, B_51]: (~v1_xboole_0(B_50) | r1_tarski(B_50, B_51))), inference(resolution, [status(thm)], [c_14, c_126])).
% 7.80/2.68  tff(c_144, plain, (![B_56, B_55]: (B_56=B_55 | ~r1_tarski(B_55, B_56) | ~v1_xboole_0(B_56))), inference(resolution, [status(thm)], [c_133, c_10])).
% 7.80/2.68  tff(c_158, plain, (![B_58, B_57]: (B_58=B_57 | ~v1_xboole_0(B_58) | ~v1_xboole_0(B_57))), inference(resolution, [status(thm)], [c_132, c_144])).
% 7.80/2.68  tff(c_161, plain, (![B_57]: (k1_xboole_0=B_57 | ~v1_xboole_0(B_57))), inference(resolution, [status(thm)], [c_8, c_158])).
% 7.80/2.68  tff(c_9384, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_9339, c_161])).
% 7.80/2.68  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.80/2.68  tff(c_279, plain, (![B_76, C_77]: (k1_relset_1(k1_xboole_0, B_76, C_77)=k1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_224])).
% 7.80/2.68  tff(c_285, plain, (![B_76]: (k1_relset_1(k1_xboole_0, B_76, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_177, c_279])).
% 7.80/2.68  tff(c_317, plain, (![A_81, B_82, C_83]: (m1_subset_1(k1_relset_1(A_81, B_82, C_83), k1_zfmisc_1(A_81)) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.80/2.68  tff(c_335, plain, (![B_76]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_76))))), inference(superposition, [status(thm), theory('equality')], [c_285, c_317])).
% 7.80/2.68  tff(c_347, plain, (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_20, c_335])).
% 7.80/2.68  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.80/2.68  tff(c_364, plain, (r1_tarski(k1_relat_1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_347, c_22])).
% 7.80/2.68  tff(c_194, plain, (![B_61]: (r1_tarski(k1_xboole_0, B_61))), inference(resolution, [status(thm)], [c_6, c_188])).
% 7.80/2.68  tff(c_205, plain, (![B_61]: (k1_xboole_0=B_61 | ~r1_tarski(B_61, k1_xboole_0))), inference(resolution, [status(thm)], [c_194, c_10])).
% 7.80/2.68  tff(c_387, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_364, c_205])).
% 7.80/2.68  tff(c_237, plain, (![A_67, C_68]: (k1_relset_1(A_67, k1_xboole_0, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_224])).
% 7.80/2.68  tff(c_243, plain, (![A_67]: (k1_relset_1(A_67, k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_177, c_237])).
% 7.80/2.68  tff(c_338, plain, (![A_67]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_67)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_67, k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_243, c_317])).
% 7.80/2.68  tff(c_349, plain, (![A_67]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_67)))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_18, c_338])).
% 7.80/2.68  tff(c_449, plain, (![A_90]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_90)))), inference(demodulation, [status(thm), theory('equality')], [c_387, c_349])).
% 7.80/2.68  tff(c_32, plain, (![A_19, B_20, C_21]: (k1_relset_1(A_19, B_20, C_21)=k1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.80/2.68  tff(c_466, plain, (![A_19, B_20]: (k1_relset_1(A_19, B_20, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_449, c_32])).
% 7.80/2.68  tff(c_479, plain, (![A_19, B_20]: (k1_relset_1(A_19, B_20, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_387, c_466])).
% 7.80/2.68  tff(c_38, plain, (![C_24, B_23]: (v1_funct_2(C_24, k1_xboole_0, B_23) | k1_relset_1(k1_xboole_0, B_23, C_24)!=k1_xboole_0 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.80/2.68  tff(c_413, plain, (![C_85, B_86]: (v1_funct_2(C_85, k1_xboole_0, B_86) | k1_relset_1(k1_xboole_0, B_86, C_85)!=k1_xboole_0 | ~m1_subset_1(C_85, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_38])).
% 7.80/2.68  tff(c_424, plain, (![B_86]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_86) | k1_relset_1(k1_xboole_0, B_86, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_177, c_413])).
% 7.80/2.68  tff(c_579, plain, (![B_86]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_86))), inference(demodulation, [status(thm), theory('equality')], [c_479, c_424])).
% 7.80/2.68  tff(c_9423, plain, (![B_86]: (v1_funct_2('#skF_2', '#skF_2', B_86))), inference(demodulation, [status(thm), theory('equality')], [c_9384, c_9384, c_579])).
% 7.80/2.68  tff(c_9430, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9384, c_9384, c_387])).
% 7.80/2.68  tff(c_9450, plain, (~v1_funct_2('#skF_2', '#skF_2', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9430, c_88])).
% 7.80/2.68  tff(c_9764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9423, c_9450])).
% 7.80/2.68  tff(c_9765, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_52])).
% 7.80/2.68  tff(c_9777, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_24, c_9765])).
% 7.80/2.68  tff(c_9801, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_9796, c_9777])).
% 7.80/2.68  tff(c_9806, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_9801])).
% 7.80/2.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/2.68  
% 7.80/2.68  Inference rules
% 7.80/2.68  ----------------------
% 7.80/2.68  #Ref     : 0
% 7.80/2.68  #Sup     : 2283
% 7.80/2.68  #Fact    : 0
% 7.80/2.68  #Define  : 0
% 7.80/2.68  #Split   : 5
% 7.80/2.68  #Chain   : 0
% 7.80/2.68  #Close   : 0
% 7.80/2.68  
% 7.80/2.68  Ordering : KBO
% 7.80/2.68  
% 7.80/2.68  Simplification rules
% 7.80/2.68  ----------------------
% 7.80/2.68  #Subsume      : 802
% 7.80/2.68  #Demod        : 2351
% 7.80/2.68  #Tautology    : 635
% 7.80/2.68  #SimpNegUnit  : 5
% 7.80/2.68  #BackRed      : 170
% 7.80/2.68  
% 7.80/2.68  #Partial instantiations: 0
% 7.80/2.68  #Strategies tried      : 1
% 7.80/2.68  
% 7.80/2.68  Timing (in seconds)
% 7.80/2.68  ----------------------
% 7.80/2.68  Preprocessing        : 0.33
% 7.80/2.68  Parsing              : 0.18
% 7.80/2.68  CNF conversion       : 0.02
% 7.80/2.68  Main loop            : 1.53
% 7.80/2.68  Inferencing          : 0.46
% 7.80/2.68  Reduction            : 0.46
% 7.80/2.68  Demodulation         : 0.33
% 7.80/2.68  BG Simplification    : 0.06
% 7.80/2.68  Subsumption          : 0.44
% 7.80/2.68  Abstraction          : 0.09
% 7.80/2.68  MUC search           : 0.00
% 7.80/2.68  Cooper               : 0.00
% 7.80/2.68  Total                : 1.91
% 7.80/2.68  Index Insertion      : 0.00
% 7.80/2.68  Index Deletion       : 0.00
% 7.80/2.68  Index Matching       : 0.00
% 7.80/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
