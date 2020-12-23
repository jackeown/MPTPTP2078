%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:16 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 284 expanded)
%              Number of leaves         :   38 ( 112 expanded)
%              Depth                    :   10
%              Number of atoms          :  223 ( 813 expanded)
%              Number of equality atoms :   48 ( 137 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_166,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v5_relat_1(C,A)
                  & v1_funct_1(C) )
               => k1_relat_1(k5_relat_1(C,B)) = k1_relat_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_funct_2)).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_146,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_95,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_98,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_95])).

tff(c_101,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_98])).

tff(c_117,plain,(
    ! [C_53,A_54,B_55] :
      ( v4_relat_1(C_53,A_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_121,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_117])).

tff(c_125,plain,(
    ! [B_61,A_62] :
      ( k1_relat_1(B_61) = A_62
      | ~ v1_partfun1(B_61,A_62)
      | ~ v4_relat_1(B_61,A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_128,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_121,c_125])).

tff(c_131,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_128])).

tff(c_132,plain,(
    ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_156,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_partfun1(C_73,A_74)
      | ~ v1_funct_2(C_73,A_74,B_75)
      | ~ v1_funct_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | v1_xboole_0(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_159,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_156])).

tff(c_162,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_159])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_132,c_162])).

tff(c_165,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_12,plain,(
    ! [A_9] :
      ( k1_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_109,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_101,c_12])).

tff(c_111,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_167,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_111])).

tff(c_60,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_178,plain,(
    ! [A_76,B_77] :
      ( k10_relat_1(A_76,k1_relat_1(B_77)) = k1_relat_1(k5_relat_1(A_76,B_77))
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_187,plain,(
    ! [A_76] :
      ( k1_relat_1(k5_relat_1(A_76,'#skF_3')) = k10_relat_1(A_76,'#skF_2')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_178])).

tff(c_192,plain,(
    ! [A_78] :
      ( k1_relat_1(k5_relat_1(A_78,'#skF_3')) = k10_relat_1(A_78,'#skF_2')
      | ~ v1_relat_1(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_187])).

tff(c_54,plain,(
    k1_relat_1(k5_relat_1('#skF_4','#skF_3')) != k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_204,plain,
    ( k10_relat_1('#skF_4','#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_54])).

tff(c_210,plain,(
    k10_relat_1('#skF_4','#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_204])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_58,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_48,plain,(
    ! [C_37,B_36] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_37),B_36,C_37),k1_relat_1(C_37))
      | v1_funct_2(C_37,k1_relat_1(C_37),B_36)
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_16,plain,(
    ! [B_12,C_14,A_11] :
      ( r2_hidden(k1_funct_1(B_12,C_14),A_11)
      | ~ r2_hidden(C_14,k1_relat_1(B_12))
      | ~ v1_funct_1(B_12)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_273,plain,(
    ! [C_95,B_96] :
      ( ~ r2_hidden(k1_funct_1(C_95,'#skF_1'(k1_relat_1(C_95),B_96,C_95)),B_96)
      | v1_funct_2(C_95,k1_relat_1(C_95),B_96)
      | ~ v1_funct_1(C_95)
      | ~ v1_relat_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_507,plain,(
    ! [B_125,A_126] :
      ( v1_funct_2(B_125,k1_relat_1(B_125),A_126)
      | ~ r2_hidden('#skF_1'(k1_relat_1(B_125),A_126,B_125),k1_relat_1(B_125))
      | ~ v1_funct_1(B_125)
      | ~ v5_relat_1(B_125,A_126)
      | ~ v1_relat_1(B_125) ) ),
    inference(resolution,[status(thm)],[c_16,c_273])).

tff(c_533,plain,(
    ! [C_37,B_36] :
      ( ~ v5_relat_1(C_37,B_36)
      | v1_funct_2(C_37,k1_relat_1(C_37),B_36)
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37) ) ),
    inference(resolution,[status(thm)],[c_48,c_507])).

tff(c_44,plain,(
    ! [C_37,B_36] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_37),B_36,C_37),k1_relat_1(C_37))
      | m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_37),B_36)))
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_427,plain,(
    ! [C_116,B_117] :
      ( ~ r2_hidden(k1_funct_1(C_116,'#skF_1'(k1_relat_1(C_116),B_117,C_116)),B_117)
      | m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_116),B_117)))
      | ~ v1_funct_1(C_116)
      | ~ v1_relat_1(C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_586,plain,(
    ! [B_133,A_134] :
      ( m1_subset_1(B_133,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_133),A_134)))
      | ~ r2_hidden('#skF_1'(k1_relat_1(B_133),A_134,B_133),k1_relat_1(B_133))
      | ~ v1_funct_1(B_133)
      | ~ v5_relat_1(B_133,A_134)
      | ~ v1_relat_1(B_133) ) ),
    inference(resolution,[status(thm)],[c_16,c_427])).

tff(c_617,plain,(
    ! [C_135,B_136] :
      ( ~ v5_relat_1(C_135,B_136)
      | m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_135),B_136)))
      | ~ v1_funct_1(C_135)
      | ~ v1_relat_1(C_135) ) ),
    inference(resolution,[status(thm)],[c_44,c_586])).

tff(c_40,plain,(
    ! [B_33,A_32,C_34] :
      ( k1_xboole_0 = B_33
      | k8_relset_1(A_32,B_33,C_34,B_33) = A_32
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_2(C_34,A_32,B_33)
      | ~ v1_funct_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_789,plain,(
    ! [B_151,C_152] :
      ( k1_xboole_0 = B_151
      | k8_relset_1(k1_relat_1(C_152),B_151,C_152,B_151) = k1_relat_1(C_152)
      | ~ v1_funct_2(C_152,k1_relat_1(C_152),B_151)
      | ~ v5_relat_1(C_152,B_151)
      | ~ v1_funct_1(C_152)
      | ~ v1_relat_1(C_152) ) ),
    inference(resolution,[status(thm)],[c_617,c_40])).

tff(c_822,plain,(
    ! [B_157,C_158] :
      ( k1_xboole_0 = B_157
      | k8_relset_1(k1_relat_1(C_158),B_157,C_158,B_157) = k1_relat_1(C_158)
      | ~ v5_relat_1(C_158,B_157)
      | ~ v1_funct_1(C_158)
      | ~ v1_relat_1(C_158) ) ),
    inference(resolution,[status(thm)],[c_533,c_789])).

tff(c_22,plain,(
    ! [A_18,B_19,C_20,D_21] :
      ( k8_relset_1(A_18,B_19,C_20,D_21) = k10_relat_1(C_20,D_21)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_649,plain,(
    ! [C_135,B_136,D_21] :
      ( k8_relset_1(k1_relat_1(C_135),B_136,C_135,D_21) = k10_relat_1(C_135,D_21)
      | ~ v5_relat_1(C_135,B_136)
      | ~ v1_funct_1(C_135)
      | ~ v1_relat_1(C_135) ) ),
    inference(resolution,[status(thm)],[c_617,c_22])).

tff(c_849,plain,(
    ! [C_159,B_160] :
      ( k10_relat_1(C_159,B_160) = k1_relat_1(C_159)
      | ~ v5_relat_1(C_159,B_160)
      | ~ v1_funct_1(C_159)
      | ~ v1_relat_1(C_159)
      | k1_xboole_0 = B_160
      | ~ v5_relat_1(C_159,B_160)
      | ~ v1_funct_1(C_159)
      | ~ v1_relat_1(C_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_822,c_649])).

tff(c_853,plain,
    ( k10_relat_1('#skF_4','#skF_2') = k1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_2'
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_849])).

tff(c_860,plain,
    ( k10_relat_1('#skF_4','#skF_2') = k1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_58,c_853])).

tff(c_862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_210,c_860])).

tff(c_863,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_871,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_2])).

tff(c_864,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_882,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_864])).

tff(c_921,plain,(
    ! [C_166,A_167,B_168] :
      ( v4_relat_1(C_166,A_167)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_925,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_921])).

tff(c_1067,plain,(
    ! [B_197,A_198] :
      ( k1_relat_1(B_197) = A_198
      | ~ v1_partfun1(B_197,A_198)
      | ~ v4_relat_1(B_197,A_198)
      | ~ v1_relat_1(B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1073,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_925,c_1067])).

tff(c_1079,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_882,c_1073])).

tff(c_1080,plain,(
    ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1079])).

tff(c_1149,plain,(
    ! [C_215,A_216,B_217] :
      ( v1_partfun1(C_215,A_216)
      | ~ v1_funct_2(C_215,A_216,B_217)
      | ~ v1_funct_1(C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217)))
      | v1_xboole_0(B_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1152,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_1149])).

tff(c_1155,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1152])).

tff(c_1157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1080,c_1155])).

tff(c_1158,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1079])).

tff(c_1179,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1158,c_68])).

tff(c_1183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_871,c_1179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.60  
% 3.54/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.54/1.61  
% 3.54/1.61  %Foreground sorts:
% 3.54/1.61  
% 3.54/1.61  
% 3.54/1.61  %Background operators:
% 3.54/1.61  
% 3.54/1.61  
% 3.54/1.61  %Foreground operators:
% 3.54/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.54/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.54/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.61  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.54/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.61  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.54/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.54/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.54/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.54/1.61  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.54/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.54/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.54/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.54/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.61  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.54/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.54/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.54/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.54/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.54/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.54/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.54/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.61  
% 3.54/1.62  tff(f_166, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t200_funct_2)).
% 3.54/1.62  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.54/1.62  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.54/1.62  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.54/1.62  tff(f_117, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.54/1.62  tff(f_89, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.54/1.62  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.54/1.62  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.54/1.62  tff(f_146, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 3.54/1.62  tff(f_65, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 3.54/1.62  tff(f_129, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 3.54/1.62  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.54/1.62  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.54/1.62  tff(c_68, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.54/1.62  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.54/1.62  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.54/1.62  tff(c_95, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.54/1.62  tff(c_98, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_95])).
% 3.54/1.62  tff(c_101, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_98])).
% 3.54/1.62  tff(c_117, plain, (![C_53, A_54, B_55]: (v4_relat_1(C_53, A_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.62  tff(c_121, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_117])).
% 3.54/1.62  tff(c_125, plain, (![B_61, A_62]: (k1_relat_1(B_61)=A_62 | ~v1_partfun1(B_61, A_62) | ~v4_relat_1(B_61, A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.54/1.62  tff(c_128, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_121, c_125])).
% 3.54/1.62  tff(c_131, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_128])).
% 3.54/1.62  tff(c_132, plain, (~v1_partfun1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_131])).
% 3.54/1.62  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.54/1.62  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.54/1.62  tff(c_156, plain, (![C_73, A_74, B_75]: (v1_partfun1(C_73, A_74) | ~v1_funct_2(C_73, A_74, B_75) | ~v1_funct_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | v1_xboole_0(B_75))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.54/1.62  tff(c_159, plain, (v1_partfun1('#skF_3', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_156])).
% 3.54/1.62  tff(c_162, plain, (v1_partfun1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_159])).
% 3.54/1.62  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_132, c_162])).
% 3.54/1.62  tff(c_165, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_131])).
% 3.54/1.62  tff(c_12, plain, (![A_9]: (k1_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.54/1.62  tff(c_109, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_101, c_12])).
% 3.54/1.62  tff(c_111, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_109])).
% 3.54/1.62  tff(c_167, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_111])).
% 3.54/1.62  tff(c_60, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.54/1.62  tff(c_178, plain, (![A_76, B_77]: (k10_relat_1(A_76, k1_relat_1(B_77))=k1_relat_1(k5_relat_1(A_76, B_77)) | ~v1_relat_1(B_77) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.54/1.62  tff(c_187, plain, (![A_76]: (k1_relat_1(k5_relat_1(A_76, '#skF_3'))=k10_relat_1(A_76, '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_76))), inference(superposition, [status(thm), theory('equality')], [c_165, c_178])).
% 3.54/1.62  tff(c_192, plain, (![A_78]: (k1_relat_1(k5_relat_1(A_78, '#skF_3'))=k10_relat_1(A_78, '#skF_2') | ~v1_relat_1(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_187])).
% 3.54/1.62  tff(c_54, plain, (k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))!=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.54/1.62  tff(c_204, plain, (k10_relat_1('#skF_4', '#skF_2')!=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_192, c_54])).
% 3.54/1.62  tff(c_210, plain, (k10_relat_1('#skF_4', '#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_204])).
% 3.54/1.62  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.54/1.62  tff(c_58, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.54/1.62  tff(c_48, plain, (![C_37, B_36]: (r2_hidden('#skF_1'(k1_relat_1(C_37), B_36, C_37), k1_relat_1(C_37)) | v1_funct_2(C_37, k1_relat_1(C_37), B_36) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.54/1.62  tff(c_16, plain, (![B_12, C_14, A_11]: (r2_hidden(k1_funct_1(B_12, C_14), A_11) | ~r2_hidden(C_14, k1_relat_1(B_12)) | ~v1_funct_1(B_12) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.54/1.62  tff(c_273, plain, (![C_95, B_96]: (~r2_hidden(k1_funct_1(C_95, '#skF_1'(k1_relat_1(C_95), B_96, C_95)), B_96) | v1_funct_2(C_95, k1_relat_1(C_95), B_96) | ~v1_funct_1(C_95) | ~v1_relat_1(C_95))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.54/1.62  tff(c_507, plain, (![B_125, A_126]: (v1_funct_2(B_125, k1_relat_1(B_125), A_126) | ~r2_hidden('#skF_1'(k1_relat_1(B_125), A_126, B_125), k1_relat_1(B_125)) | ~v1_funct_1(B_125) | ~v5_relat_1(B_125, A_126) | ~v1_relat_1(B_125))), inference(resolution, [status(thm)], [c_16, c_273])).
% 3.54/1.62  tff(c_533, plain, (![C_37, B_36]: (~v5_relat_1(C_37, B_36) | v1_funct_2(C_37, k1_relat_1(C_37), B_36) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37))), inference(resolution, [status(thm)], [c_48, c_507])).
% 3.54/1.62  tff(c_44, plain, (![C_37, B_36]: (r2_hidden('#skF_1'(k1_relat_1(C_37), B_36, C_37), k1_relat_1(C_37)) | m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_37), B_36))) | ~v1_funct_1(C_37) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.54/1.62  tff(c_427, plain, (![C_116, B_117]: (~r2_hidden(k1_funct_1(C_116, '#skF_1'(k1_relat_1(C_116), B_117, C_116)), B_117) | m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_116), B_117))) | ~v1_funct_1(C_116) | ~v1_relat_1(C_116))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.54/1.62  tff(c_586, plain, (![B_133, A_134]: (m1_subset_1(B_133, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_133), A_134))) | ~r2_hidden('#skF_1'(k1_relat_1(B_133), A_134, B_133), k1_relat_1(B_133)) | ~v1_funct_1(B_133) | ~v5_relat_1(B_133, A_134) | ~v1_relat_1(B_133))), inference(resolution, [status(thm)], [c_16, c_427])).
% 3.54/1.62  tff(c_617, plain, (![C_135, B_136]: (~v5_relat_1(C_135, B_136) | m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_135), B_136))) | ~v1_funct_1(C_135) | ~v1_relat_1(C_135))), inference(resolution, [status(thm)], [c_44, c_586])).
% 3.54/1.62  tff(c_40, plain, (![B_33, A_32, C_34]: (k1_xboole_0=B_33 | k8_relset_1(A_32, B_33, C_34, B_33)=A_32 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_2(C_34, A_32, B_33) | ~v1_funct_1(C_34))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.54/1.62  tff(c_789, plain, (![B_151, C_152]: (k1_xboole_0=B_151 | k8_relset_1(k1_relat_1(C_152), B_151, C_152, B_151)=k1_relat_1(C_152) | ~v1_funct_2(C_152, k1_relat_1(C_152), B_151) | ~v5_relat_1(C_152, B_151) | ~v1_funct_1(C_152) | ~v1_relat_1(C_152))), inference(resolution, [status(thm)], [c_617, c_40])).
% 3.54/1.62  tff(c_822, plain, (![B_157, C_158]: (k1_xboole_0=B_157 | k8_relset_1(k1_relat_1(C_158), B_157, C_158, B_157)=k1_relat_1(C_158) | ~v5_relat_1(C_158, B_157) | ~v1_funct_1(C_158) | ~v1_relat_1(C_158))), inference(resolution, [status(thm)], [c_533, c_789])).
% 3.54/1.62  tff(c_22, plain, (![A_18, B_19, C_20, D_21]: (k8_relset_1(A_18, B_19, C_20, D_21)=k10_relat_1(C_20, D_21) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.54/1.62  tff(c_649, plain, (![C_135, B_136, D_21]: (k8_relset_1(k1_relat_1(C_135), B_136, C_135, D_21)=k10_relat_1(C_135, D_21) | ~v5_relat_1(C_135, B_136) | ~v1_funct_1(C_135) | ~v1_relat_1(C_135))), inference(resolution, [status(thm)], [c_617, c_22])).
% 3.54/1.62  tff(c_849, plain, (![C_159, B_160]: (k10_relat_1(C_159, B_160)=k1_relat_1(C_159) | ~v5_relat_1(C_159, B_160) | ~v1_funct_1(C_159) | ~v1_relat_1(C_159) | k1_xboole_0=B_160 | ~v5_relat_1(C_159, B_160) | ~v1_funct_1(C_159) | ~v1_relat_1(C_159))), inference(superposition, [status(thm), theory('equality')], [c_822, c_649])).
% 3.54/1.62  tff(c_853, plain, (k10_relat_1('#skF_4', '#skF_2')=k1_relat_1('#skF_4') | k1_xboole_0='#skF_2' | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_849])).
% 3.54/1.62  tff(c_860, plain, (k10_relat_1('#skF_4', '#skF_2')=k1_relat_1('#skF_4') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_58, c_853])).
% 3.54/1.62  tff(c_862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_210, c_860])).
% 3.54/1.62  tff(c_863, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_109])).
% 3.54/1.62  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.54/1.62  tff(c_871, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_863, c_2])).
% 3.54/1.62  tff(c_864, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_109])).
% 3.54/1.62  tff(c_882, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_863, c_864])).
% 3.54/1.62  tff(c_921, plain, (![C_166, A_167, B_168]: (v4_relat_1(C_166, A_167) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.62  tff(c_925, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_921])).
% 3.54/1.62  tff(c_1067, plain, (![B_197, A_198]: (k1_relat_1(B_197)=A_198 | ~v1_partfun1(B_197, A_198) | ~v4_relat_1(B_197, A_198) | ~v1_relat_1(B_197))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.54/1.62  tff(c_1073, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_925, c_1067])).
% 3.54/1.62  tff(c_1079, plain, ('#skF_2'='#skF_3' | ~v1_partfun1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_882, c_1073])).
% 3.54/1.62  tff(c_1080, plain, (~v1_partfun1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_1079])).
% 3.54/1.62  tff(c_1149, plain, (![C_215, A_216, B_217]: (v1_partfun1(C_215, A_216) | ~v1_funct_2(C_215, A_216, B_217) | ~v1_funct_1(C_215) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))) | v1_xboole_0(B_217))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.54/1.62  tff(c_1152, plain, (v1_partfun1('#skF_3', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_1149])).
% 3.54/1.62  tff(c_1155, plain, (v1_partfun1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1152])).
% 3.54/1.62  tff(c_1157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1080, c_1155])).
% 3.54/1.62  tff(c_1158, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1079])).
% 3.54/1.62  tff(c_1179, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1158, c_68])).
% 3.54/1.62  tff(c_1183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_871, c_1179])).
% 3.54/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.62  
% 3.54/1.62  Inference rules
% 3.54/1.62  ----------------------
% 3.54/1.62  #Ref     : 0
% 3.54/1.62  #Sup     : 232
% 3.54/1.62  #Fact    : 0
% 3.54/1.62  #Define  : 0
% 3.54/1.62  #Split   : 10
% 3.54/1.62  #Chain   : 0
% 3.54/1.62  #Close   : 0
% 3.54/1.62  
% 3.54/1.63  Ordering : KBO
% 3.54/1.63  
% 3.54/1.63  Simplification rules
% 3.54/1.63  ----------------------
% 3.54/1.63  #Subsume      : 41
% 3.54/1.63  #Demod        : 217
% 3.54/1.63  #Tautology    : 85
% 3.54/1.63  #SimpNegUnit  : 19
% 3.54/1.63  #BackRed      : 20
% 3.54/1.63  
% 3.54/1.63  #Partial instantiations: 0
% 3.54/1.63  #Strategies tried      : 1
% 3.54/1.63  
% 3.54/1.63  Timing (in seconds)
% 3.54/1.63  ----------------------
% 3.99/1.63  Preprocessing        : 0.36
% 3.99/1.63  Parsing              : 0.19
% 3.99/1.63  CNF conversion       : 0.02
% 3.99/1.63  Main loop            : 0.49
% 3.99/1.63  Inferencing          : 0.19
% 3.99/1.63  Reduction            : 0.15
% 3.99/1.63  Demodulation         : 0.11
% 3.99/1.63  BG Simplification    : 0.03
% 3.99/1.63  Subsumption          : 0.08
% 3.99/1.63  Abstraction          : 0.03
% 3.99/1.63  MUC search           : 0.00
% 3.99/1.63  Cooper               : 0.00
% 3.99/1.63  Total                : 0.90
% 3.99/1.63  Index Insertion      : 0.00
% 3.99/1.63  Index Deletion       : 0.00
% 3.99/1.63  Index Matching       : 0.00
% 3.99/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
