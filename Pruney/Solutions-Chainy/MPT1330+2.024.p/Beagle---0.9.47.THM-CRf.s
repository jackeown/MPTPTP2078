%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:12 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 549 expanded)
%              Number of leaves         :   48 ( 208 expanded)
%              Depth                    :   11
%              Number of atoms          :  174 (1242 expanded)
%              Number of equality atoms :   73 ( 538 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_98,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_74,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_struct_0(B) = k1_xboole_0
                   => k2_struct_0(A) = k1_xboole_0 )
                 => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_struct_0(B)) = k2_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_119,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(c_20,plain,(
    ! [A_14] : k10_relat_1(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1786,plain,(
    ! [A_223,B_224,C_225,D_226] :
      ( k8_relset_1(A_223,B_224,C_225,D_226) = k10_relat_1(C_225,D_226)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1791,plain,(
    ! [A_223,B_224,D_226] : k8_relset_1(A_223,B_224,k1_xboole_0,D_226) = k10_relat_1(k1_xboole_0,D_226) ),
    inference(resolution,[status(thm)],[c_8,c_1786])).

tff(c_1810,plain,(
    ! [A_227,B_228,D_229] : k8_relset_1(A_227,B_228,k1_xboole_0,D_229) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1791])).

tff(c_1127,plain,(
    ! [A_153] : k6_relat_1(A_153) = k6_partfun1(A_153) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1133,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1127,c_30])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_68,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_175,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_183,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_175])).

tff(c_66,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_182,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_175])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_194,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_182,c_60])).

tff(c_195,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_198,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_194,c_195])).

tff(c_204,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_198])).

tff(c_218,plain,(
    ! [C_58,B_59,A_60] :
      ( v5_relat_1(C_58,B_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_232,plain,(
    v5_relat_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_194,c_218])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_46,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    ! [B_20,A_19] :
      ( k5_relat_1(B_20,k6_relat_1(A_19)) = B_20
      | ~ r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_349,plain,(
    ! [B_87,A_88] :
      ( k5_relat_1(B_87,k6_partfun1(A_88)) = B_87
      | ~ r1_tarski(k2_relat_1(B_87),A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_28])).

tff(c_359,plain,(
    ! [B_11,A_10] :
      ( k5_relat_1(B_11,k6_partfun1(A_10)) = B_11
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_349])).

tff(c_32,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_70,plain,(
    ! [A_21] : v1_relat_1(k6_partfun1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_32])).

tff(c_24,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_73,plain,(
    ! [A_18] : k1_relat_1(k6_partfun1(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_24])).

tff(c_805,plain,(
    ! [A_132,B_133] :
      ( k10_relat_1(A_132,k1_relat_1(B_133)) = k1_relat_1(k5_relat_1(A_132,B_133))
      | ~ v1_relat_1(B_133)
      | ~ v1_relat_1(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_825,plain,(
    ! [A_132,A_18] :
      ( k1_relat_1(k5_relat_1(A_132,k6_partfun1(A_18))) = k10_relat_1(A_132,A_18)
      | ~ v1_relat_1(k6_partfun1(A_18))
      | ~ v1_relat_1(A_132) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_805])).

tff(c_923,plain,(
    ! [A_137,A_138] :
      ( k1_relat_1(k5_relat_1(A_137,k6_partfun1(A_138))) = k10_relat_1(A_137,A_138)
      | ~ v1_relat_1(A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_825])).

tff(c_992,plain,(
    ! [B_141,A_142] :
      ( k10_relat_1(B_141,A_142) = k1_relat_1(B_141)
      | ~ v1_relat_1(B_141)
      | ~ v5_relat_1(B_141,A_142)
      | ~ v1_relat_1(B_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_923])).

tff(c_998,plain,
    ( k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_232,c_992])).

tff(c_1007,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_998])).

tff(c_285,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_299,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_194,c_285])).

tff(c_479,plain,(
    ! [B_100,A_101] :
      ( k1_relat_1(B_100) = A_101
      | ~ v1_partfun1(B_100,A_101)
      | ~ v4_relat_1(B_100,A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_482,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_299,c_479])).

tff(c_488,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_482])).

tff(c_502,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_488])).

tff(c_58,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_98,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_62,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_184,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_62])).

tff(c_193,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_184])).

tff(c_733,plain,(
    ! [B_128,C_129,A_130] :
      ( k1_xboole_0 = B_128
      | v1_partfun1(C_129,A_130)
      | ~ v1_funct_2(C_129,A_130,B_128)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_130,B_128)))
      | ~ v1_funct_1(C_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_736,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_194,c_733])).

tff(c_749,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_193,c_736])).

tff(c_751,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_502,c_98,c_749])).

tff(c_752,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_488])).

tff(c_757,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_194])).

tff(c_1076,plain,(
    ! [A_147,B_148,C_149,D_150] :
      ( k8_relset_1(A_147,B_148,C_149,D_150) = k10_relat_1(C_149,D_150)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1086,plain,(
    ! [D_150] : k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',D_150) = k10_relat_1('#skF_3',D_150) ),
    inference(resolution,[status(thm)],[c_757,c_1076])).

tff(c_56,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_253,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_182,c_56])).

tff(c_756,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_752,c_253])).

tff(c_1089,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1086,c_756])).

tff(c_1092,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1007,c_1089])).

tff(c_1094,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1179,plain,(
    ! [A_157] :
      ( u1_struct_0(A_157) = k2_struct_0(A_157)
      | ~ l1_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1182,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1179])).

tff(c_1187,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1094,c_1182])).

tff(c_1200,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1187,c_60])).

tff(c_1399,plain,(
    ! [A_198,B_199] :
      ( k8_relset_1(A_198,A_198,k6_partfun1(A_198),B_199) = B_199
      | ~ m1_subset_1(B_199,k1_zfmisc_1(A_198)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1401,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1200,c_1399])).

tff(c_1405,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1133,c_1401])).

tff(c_1814,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1810,c_1405])).

tff(c_1795,plain,(
    ! [A_223,B_224,D_226] : k8_relset_1(A_223,B_224,k1_xboole_0,D_226) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1791])).

tff(c_1821,plain,(
    ! [A_223,B_224,D_226] : k8_relset_1(A_223,B_224,'#skF_3',D_226) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1814,c_1814,c_1795])).

tff(c_1093,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1185,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_1179])).

tff(c_1189,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_1185])).

tff(c_1264,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_1187,c_1094,c_1093,c_56])).

tff(c_1843,plain,(
    k8_relset_1('#skF_3','#skF_3','#skF_3','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1814,c_1814,c_1814,c_1814,c_1264])).

tff(c_2186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1821,c_1843])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:22:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.66/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.64  
% 3.66/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.64  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.66/1.64  
% 3.66/1.64  %Foreground sorts:
% 3.66/1.64  
% 3.66/1.64  
% 3.66/1.64  %Background operators:
% 3.66/1.64  
% 3.66/1.64  
% 3.66/1.64  %Foreground operators:
% 3.66/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.66/1.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.66/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.66/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.66/1.64  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.66/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.66/1.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.66/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.66/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.66/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.66/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.66/1.64  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.66/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.66/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.66/1.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.66/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.66/1.64  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.66/1.64  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.66/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.66/1.64  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.66/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.66/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.66/1.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.66/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.66/1.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.66/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.66/1.64  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.66/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.66/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.66/1.64  
% 4.03/1.67  tff(f_56, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 4.03/1.67  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.03/1.67  tff(f_88, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.03/1.67  tff(f_98, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.03/1.67  tff(f_74, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 4.03/1.67  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.03/1.67  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.03/1.67  tff(f_142, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 4.03/1.67  tff(f_123, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.03/1.67  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.03/1.67  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.03/1.67  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.03/1.67  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 4.03/1.67  tff(f_78, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.03/1.67  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.03/1.67  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 4.03/1.67  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.03/1.67  tff(f_115, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 4.03/1.67  tff(f_119, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 4.03/1.67  tff(c_20, plain, (![A_14]: (k10_relat_1(k1_xboole_0, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.03/1.67  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.03/1.67  tff(c_1786, plain, (![A_223, B_224, C_225, D_226]: (k8_relset_1(A_223, B_224, C_225, D_226)=k10_relat_1(C_225, D_226) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.03/1.67  tff(c_1791, plain, (![A_223, B_224, D_226]: (k8_relset_1(A_223, B_224, k1_xboole_0, D_226)=k10_relat_1(k1_xboole_0, D_226))), inference(resolution, [status(thm)], [c_8, c_1786])).
% 4.03/1.67  tff(c_1810, plain, (![A_227, B_228, D_229]: (k8_relset_1(A_227, B_228, k1_xboole_0, D_229)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1791])).
% 4.03/1.67  tff(c_1127, plain, (![A_153]: (k6_relat_1(A_153)=k6_partfun1(A_153))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.03/1.67  tff(c_30, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.03/1.67  tff(c_1133, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1127, c_30])).
% 4.03/1.67  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.03/1.67  tff(c_18, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.03/1.67  tff(c_68, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.03/1.67  tff(c_175, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.03/1.67  tff(c_183, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_175])).
% 4.03/1.67  tff(c_66, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.03/1.67  tff(c_182, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_175])).
% 4.03/1.67  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.03/1.67  tff(c_194, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_182, c_60])).
% 4.03/1.67  tff(c_195, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.03/1.67  tff(c_198, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_194, c_195])).
% 4.03/1.67  tff(c_204, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_198])).
% 4.03/1.67  tff(c_218, plain, (![C_58, B_59, A_60]: (v5_relat_1(C_58, B_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.03/1.67  tff(c_232, plain, (v5_relat_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_194, c_218])).
% 4.03/1.67  tff(c_16, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.03/1.67  tff(c_46, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.03/1.67  tff(c_28, plain, (![B_20, A_19]: (k5_relat_1(B_20, k6_relat_1(A_19))=B_20 | ~r1_tarski(k2_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.03/1.67  tff(c_349, plain, (![B_87, A_88]: (k5_relat_1(B_87, k6_partfun1(A_88))=B_87 | ~r1_tarski(k2_relat_1(B_87), A_88) | ~v1_relat_1(B_87))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_28])).
% 4.03/1.67  tff(c_359, plain, (![B_11, A_10]: (k5_relat_1(B_11, k6_partfun1(A_10))=B_11 | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_16, c_349])).
% 4.03/1.67  tff(c_32, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.03/1.67  tff(c_70, plain, (![A_21]: (v1_relat_1(k6_partfun1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_32])).
% 4.03/1.67  tff(c_24, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.03/1.67  tff(c_73, plain, (![A_18]: (k1_relat_1(k6_partfun1(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_24])).
% 4.03/1.67  tff(c_805, plain, (![A_132, B_133]: (k10_relat_1(A_132, k1_relat_1(B_133))=k1_relat_1(k5_relat_1(A_132, B_133)) | ~v1_relat_1(B_133) | ~v1_relat_1(A_132))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.03/1.67  tff(c_825, plain, (![A_132, A_18]: (k1_relat_1(k5_relat_1(A_132, k6_partfun1(A_18)))=k10_relat_1(A_132, A_18) | ~v1_relat_1(k6_partfun1(A_18)) | ~v1_relat_1(A_132))), inference(superposition, [status(thm), theory('equality')], [c_73, c_805])).
% 4.03/1.67  tff(c_923, plain, (![A_137, A_138]: (k1_relat_1(k5_relat_1(A_137, k6_partfun1(A_138)))=k10_relat_1(A_137, A_138) | ~v1_relat_1(A_137))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_825])).
% 4.03/1.67  tff(c_992, plain, (![B_141, A_142]: (k10_relat_1(B_141, A_142)=k1_relat_1(B_141) | ~v1_relat_1(B_141) | ~v5_relat_1(B_141, A_142) | ~v1_relat_1(B_141))), inference(superposition, [status(thm), theory('equality')], [c_359, c_923])).
% 4.03/1.67  tff(c_998, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_232, c_992])).
% 4.03/1.67  tff(c_1007, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_998])).
% 4.03/1.67  tff(c_285, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.03/1.67  tff(c_299, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_194, c_285])).
% 4.03/1.67  tff(c_479, plain, (![B_100, A_101]: (k1_relat_1(B_100)=A_101 | ~v1_partfun1(B_100, A_101) | ~v4_relat_1(B_100, A_101) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.03/1.67  tff(c_482, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_299, c_479])).
% 4.03/1.67  tff(c_488, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_482])).
% 4.03/1.67  tff(c_502, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_488])).
% 4.03/1.67  tff(c_58, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.03/1.67  tff(c_98, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 4.03/1.67  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.03/1.67  tff(c_62, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.03/1.67  tff(c_184, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_62])).
% 4.03/1.67  tff(c_193, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_184])).
% 4.03/1.67  tff(c_733, plain, (![B_128, C_129, A_130]: (k1_xboole_0=B_128 | v1_partfun1(C_129, A_130) | ~v1_funct_2(C_129, A_130, B_128) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_130, B_128))) | ~v1_funct_1(C_129))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.03/1.67  tff(c_736, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_194, c_733])).
% 4.03/1.67  tff(c_749, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_193, c_736])).
% 4.03/1.67  tff(c_751, plain, $false, inference(negUnitSimplification, [status(thm)], [c_502, c_98, c_749])).
% 4.03/1.67  tff(c_752, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_488])).
% 4.03/1.67  tff(c_757, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_752, c_194])).
% 4.03/1.67  tff(c_1076, plain, (![A_147, B_148, C_149, D_150]: (k8_relset_1(A_147, B_148, C_149, D_150)=k10_relat_1(C_149, D_150) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.03/1.67  tff(c_1086, plain, (![D_150]: (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', D_150)=k10_relat_1('#skF_3', D_150))), inference(resolution, [status(thm)], [c_757, c_1076])).
% 4.03/1.67  tff(c_56, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.03/1.67  tff(c_253, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_182, c_56])).
% 4.03/1.67  tff(c_756, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_752, c_752, c_253])).
% 4.03/1.67  tff(c_1089, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1086, c_756])).
% 4.03/1.67  tff(c_1092, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1007, c_1089])).
% 4.03/1.67  tff(c_1094, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 4.03/1.67  tff(c_1179, plain, (![A_157]: (u1_struct_0(A_157)=k2_struct_0(A_157) | ~l1_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.03/1.67  tff(c_1182, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1179])).
% 4.03/1.67  tff(c_1187, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1094, c_1182])).
% 4.03/1.67  tff(c_1200, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1187, c_60])).
% 4.03/1.67  tff(c_1399, plain, (![A_198, B_199]: (k8_relset_1(A_198, A_198, k6_partfun1(A_198), B_199)=B_199 | ~m1_subset_1(B_199, k1_zfmisc_1(A_198)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.03/1.67  tff(c_1401, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, k6_partfun1(k1_xboole_0), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1200, c_1399])).
% 4.03/1.67  tff(c_1405, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, k1_xboole_0, '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1133, c_1401])).
% 4.03/1.67  tff(c_1814, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1810, c_1405])).
% 4.03/1.67  tff(c_1795, plain, (![A_223, B_224, D_226]: (k8_relset_1(A_223, B_224, k1_xboole_0, D_226)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1791])).
% 4.03/1.67  tff(c_1821, plain, (![A_223, B_224, D_226]: (k8_relset_1(A_223, B_224, '#skF_3', D_226)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1814, c_1814, c_1795])).
% 4.03/1.67  tff(c_1093, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 4.03/1.67  tff(c_1185, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_1179])).
% 4.03/1.67  tff(c_1189, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_1185])).
% 4.03/1.67  tff(c_1264, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1189, c_1187, c_1094, c_1093, c_56])).
% 4.03/1.67  tff(c_1843, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1814, c_1814, c_1814, c_1814, c_1264])).
% 4.03/1.67  tff(c_2186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1821, c_1843])).
% 4.03/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.67  
% 4.03/1.67  Inference rules
% 4.03/1.67  ----------------------
% 4.03/1.67  #Ref     : 0
% 4.03/1.67  #Sup     : 476
% 4.03/1.67  #Fact    : 0
% 4.03/1.67  #Define  : 0
% 4.03/1.67  #Split   : 2
% 4.03/1.67  #Chain   : 0
% 4.03/1.67  #Close   : 0
% 4.03/1.67  
% 4.03/1.67  Ordering : KBO
% 4.03/1.67  
% 4.03/1.67  Simplification rules
% 4.03/1.67  ----------------------
% 4.03/1.67  #Subsume      : 27
% 4.03/1.67  #Demod        : 475
% 4.03/1.67  #Tautology    : 310
% 4.03/1.67  #SimpNegUnit  : 1
% 4.03/1.67  #BackRed      : 56
% 4.03/1.67  
% 4.03/1.67  #Partial instantiations: 0
% 4.03/1.67  #Strategies tried      : 1
% 4.03/1.67  
% 4.03/1.67  Timing (in seconds)
% 4.03/1.67  ----------------------
% 4.03/1.67  Preprocessing        : 0.33
% 4.03/1.67  Parsing              : 0.18
% 4.03/1.67  CNF conversion       : 0.02
% 4.03/1.67  Main loop            : 0.54
% 4.03/1.67  Inferencing          : 0.19
% 4.03/1.67  Reduction            : 0.20
% 4.03/1.67  Demodulation         : 0.14
% 4.03/1.68  BG Simplification    : 0.02
% 4.03/1.68  Subsumption          : 0.07
% 4.03/1.68  Abstraction          : 0.03
% 4.03/1.68  MUC search           : 0.00
% 4.03/1.68  Cooper               : 0.00
% 4.03/1.68  Total                : 0.93
% 4.03/1.68  Index Insertion      : 0.00
% 4.03/1.68  Index Deletion       : 0.00
% 4.03/1.68  Index Matching       : 0.00
% 4.03/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
