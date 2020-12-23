%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:36 EST 2020

% Result     : Theorem 6.40s
% Output     : CNFRefutation 6.40s
% Verified   : 
% Statistics : Number of formulae       :  189 (25226 expanded)
%              Number of leaves         :   58 (8770 expanded)
%              Depth                    :   29
%              Number of atoms          :  412 (71800 expanded)
%              Number of equality atoms :  111 (15830 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_286,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_238,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_154,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_252,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_150,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_176,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_168,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_192,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_224,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_208,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_178,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_127,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_144,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_234,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_264,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_110,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_116,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_162,plain,(
    ! [A_71] :
      ( u1_struct_0(A_71) = k2_struct_0(A_71)
      | ~ l1_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_170,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_116,c_162])).

tff(c_112,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_169,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_112,c_162])).

tff(c_106,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_180,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_169,c_106])).

tff(c_482,plain,(
    ! [A_117,B_118,C_119] :
      ( k2_relset_1(A_117,B_118,C_119) = k2_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_492,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_180,c_482])).

tff(c_104,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_214,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_169,c_104])).

tff(c_493,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_214])).

tff(c_114,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_182,plain,(
    ! [A_72] :
      ( ~ v1_xboole_0(u1_struct_0(A_72))
      | ~ l1_struct_0(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_188,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_182])).

tff(c_192,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_188])).

tff(c_193,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_192])).

tff(c_501,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_193])).

tff(c_24,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_219,plain,(
    ! [B_76,A_77] :
      ( v1_relat_1(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_77))
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_222,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_180,c_219])).

tff(c_225,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_222])).

tff(c_354,plain,(
    ! [C_95,A_96,B_97] :
      ( v4_relat_1(C_95,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_364,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_180,c_354])).

tff(c_469,plain,(
    ! [B_115,A_116] :
      ( k1_relat_1(B_115) = A_116
      | ~ v1_partfun1(B_115,A_116)
      | ~ v4_relat_1(B_115,A_116)
      | ~ v1_relat_1(B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_472,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_364,c_469])).

tff(c_478,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_472])).

tff(c_481,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_478])).

tff(c_108,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_171,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_108])).

tff(c_181,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_171])).

tff(c_502,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_181])).

tff(c_503,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_180])).

tff(c_602,plain,(
    ! [C_127,A_128,B_129] :
      ( v1_partfun1(C_127,A_128)
      | ~ v1_funct_2(C_127,A_128,B_129)
      | ~ v1_funct_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | v1_xboole_0(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_605,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_503,c_602])).

tff(c_617,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_502,c_605])).

tff(c_619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_501,c_481,c_617])).

tff(c_620,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_627,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_180])).

tff(c_723,plain,(
    ! [A_133,B_134,C_135] :
      ( k2_relset_1(A_133,B_134,C_135) = k2_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_737,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_627,c_723])).

tff(c_624,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_214])).

tff(c_738,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_624])).

tff(c_626,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_181])).

tff(c_745,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_626])).

tff(c_746,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_627])).

tff(c_1744,plain,(
    ! [A_216,B_217,C_218,D_219] :
      ( r2_funct_2(A_216,B_217,C_218,C_218)
      | ~ m1_subset_1(D_219,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217)))
      | ~ v1_funct_2(D_219,A_216,B_217)
      | ~ v1_funct_1(D_219)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217)))
      | ~ v1_funct_2(C_218,A_216,B_217)
      | ~ v1_funct_1(C_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1748,plain,(
    ! [C_218] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_218,C_218)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_218,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_218) ) ),
    inference(resolution,[status(thm)],[c_746,c_1744])).

tff(c_1813,plain,(
    ! [C_222] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_222,C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_222,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_745,c_1748])).

tff(c_1818,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_746,c_1813])).

tff(c_1825,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_745,c_1818])).

tff(c_226,plain,(
    ! [A_78] :
      ( k2_relat_1(A_78) = k1_xboole_0
      | k1_relat_1(A_78) != k1_xboole_0
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_242,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_225,c_226])).

tff(c_271,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_273,plain,(
    ! [A_82] :
      ( k1_relat_1(A_82) = k1_xboole_0
      | k2_relat_1(A_82) != k1_xboole_0
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_276,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_225,c_273])).

tff(c_291,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_276])).

tff(c_743,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_737])).

tff(c_102,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_1428,plain,(
    ! [A_210,C_211,B_212] :
      ( k6_partfun1(A_210) = k5_relat_1(C_211,k2_funct_1(C_211))
      | k1_xboole_0 = B_212
      | ~ v2_funct_1(C_211)
      | k2_relset_1(A_210,B_212,C_211) != B_212
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_210,B_212)))
      | ~ v1_funct_2(C_211,A_210,B_212)
      | ~ v1_funct_1(C_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_1432,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_746,c_1428])).

tff(c_1442,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_745,c_743,c_102,c_1432])).

tff(c_1443,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_1442])).

tff(c_34,plain,(
    ! [A_15] :
      ( v1_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1042,plain,(
    ! [C_167,A_168,B_169] :
      ( v1_funct_1(k2_funct_1(C_167))
      | k2_relset_1(A_168,B_169,C_167) != B_169
      | ~ v2_funct_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ v1_funct_2(C_167,A_168,B_169)
      | ~ v1_funct_1(C_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_1045,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_746,c_1042])).

tff(c_1057,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_745,c_102,c_743,c_1045])).

tff(c_72,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_38,plain,(
    ! [A_16] : v2_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_118,plain,(
    ! [A_16] : v2_funct_1(k6_partfun1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_38])).

tff(c_48,plain,(
    ! [A_21,B_23] :
      ( v2_funct_1(A_21)
      | k2_relat_1(B_23) != k1_relat_1(A_21)
      | ~ v2_funct_1(k5_relat_1(B_23,A_21))
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1449,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1(k1_relat_1('#skF_3')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1443,c_48])).

tff(c_1456,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_225,c_110,c_118,c_1449])).

tff(c_1460,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1456])).

tff(c_1463,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1460])).

tff(c_1467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_110,c_1463])).

tff(c_1469,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1456])).

tff(c_54,plain,(
    ! [A_24] :
      ( k1_relat_1(k2_funct_1(A_24)) = k2_relat_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1468,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1456])).

tff(c_1478,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1468])).

tff(c_1481,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1478])).

tff(c_1485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_110,c_102,c_1481])).

tff(c_1486,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1468])).

tff(c_1487,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1468])).

tff(c_26,plain,(
    ! [A_13] :
      ( k9_relat_1(A_13,k1_relat_1(A_13)) = k2_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1523,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1487,c_26])).

tff(c_1553,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1469,c_1523])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_770,plain,(
    ! [A_136,B_137] :
      ( k9_relat_1(k2_funct_1(A_136),k9_relat_1(A_136,B_137)) = B_137
      | ~ r1_tarski(B_137,k1_relat_1(A_136))
      | ~ v2_funct_1(A_136)
      | ~ v1_funct_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_785,plain,(
    ! [A_13] :
      ( k9_relat_1(k2_funct_1(A_13),k2_relat_1(A_13)) = k1_relat_1(A_13)
      | ~ r1_tarski(k1_relat_1(A_13),k1_relat_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_770])).

tff(c_789,plain,(
    ! [A_13] :
      ( k9_relat_1(k2_funct_1(A_13),k2_relat_1(A_13)) = k1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_785])).

tff(c_1611,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1553,c_789])).

tff(c_1621,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_110,c_102,c_1611])).

tff(c_56,plain,(
    ! [A_25,B_27] :
      ( k2_funct_1(A_25) = B_27
      | k6_relat_1(k2_relat_1(A_25)) != k5_relat_1(B_27,A_25)
      | k2_relat_1(B_27) != k1_relat_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_117,plain,(
    ! [A_25,B_27] :
      ( k2_funct_1(A_25) = B_27
      | k6_partfun1(k2_relat_1(A_25)) != k5_relat_1(B_27,A_25)
      | k2_relat_1(B_27) != k1_relat_1(A_25)
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_56])).

tff(c_1647,plain,(
    ! [B_27] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_27
      | k5_relat_1(B_27,k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3'))
      | k2_relat_1(B_27) != k1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1621,c_117])).

tff(c_3868,plain,(
    ! [B_286] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_286
      | k5_relat_1(B_286,k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3'))
      | k2_relat_1(B_286) != k2_relat_1('#skF_3')
      | ~ v1_funct_1(B_286)
      | ~ v1_relat_1(B_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1469,c_1057,c_1486,c_1487,c_1647])).

tff(c_3874,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1443,c_3868])).

tff(c_3881,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_110,c_3874])).

tff(c_1155,plain,(
    ! [C_187,B_188,A_189] :
      ( v1_funct_2(k2_funct_1(C_187),B_188,A_189)
      | k2_relset_1(A_189,B_188,C_187) != B_188
      | ~ v2_funct_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_189,B_188)))
      | ~ v1_funct_2(C_187,A_189,B_188)
      | ~ v1_funct_1(C_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_1158,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_746,c_1155])).

tff(c_1170,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_745,c_102,c_743,c_1158])).

tff(c_86,plain,(
    ! [A_51] :
      ( m1_subset_1(A_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_51),k2_relat_1(A_51))))
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_736,plain,(
    ! [A_51] :
      ( k2_relset_1(k1_relat_1(A_51),k2_relat_1(A_51),A_51) = k2_relat_1(A_51)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_86,c_723])).

tff(c_1665,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1621,c_736])).

tff(c_1703,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1469,c_1057,c_1621,c_1487,c_1665])).

tff(c_1671,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1621,c_86])).

tff(c_1707,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1469,c_1057,c_1487,c_1671])).

tff(c_98,plain,(
    ! [A_55,B_56,C_57] :
      ( k2_tops_2(A_55,B_56,C_57) = k2_funct_1(C_57)
      | ~ v2_funct_1(C_57)
      | k2_relset_1(A_55,B_56,C_57) != B_56
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56)))
      | ~ v1_funct_2(C_57,A_55,B_56)
      | ~ v1_funct_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_1901,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1707,c_98])).

tff(c_1936,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_1170,c_1703,c_1486,c_1901])).

tff(c_1214,plain,(
    ! [A_195,B_196,C_197] :
      ( k2_tops_2(A_195,B_196,C_197) = k2_funct_1(C_197)
      | ~ v2_funct_1(C_197)
      | k2_relset_1(A_195,B_196,C_197) != B_196
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196)))
      | ~ v1_funct_2(C_197,A_195,B_196)
      | ~ v1_funct_1(C_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_264])).

tff(c_1217,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_746,c_1214])).

tff(c_1229,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_745,c_743,c_102,c_1217])).

tff(c_100,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_272,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_170,c_170,c_169,c_169,c_169,c_100])).

tff(c_623,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_620,c_620,c_272])).

tff(c_744,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_738,c_738,c_623])).

tff(c_1231,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1229,c_744])).

tff(c_2307,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1936,c_1231])).

tff(c_3899,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3881,c_2307])).

tff(c_3921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1825,c_3899])).

tff(c_3922,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_4270,plain,(
    ! [A_327,B_328,C_329] :
      ( k2_relset_1(A_327,B_328,C_329) = k2_relat_1(C_329)
      | ~ m1_subset_1(C_329,k1_zfmisc_1(k2_zfmisc_1(A_327,B_328))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_4276,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_180,c_4270])).

tff(c_4285,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3922,c_4276])).

tff(c_4289,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4285,c_214])).

tff(c_4296,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4289,c_193])).

tff(c_4302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:50:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.40/2.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.40/2.21  
% 6.40/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.40/2.21  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.40/2.21  
% 6.40/2.21  %Foreground sorts:
% 6.40/2.21  
% 6.40/2.21  
% 6.40/2.21  %Background operators:
% 6.40/2.21  
% 6.40/2.21  
% 6.40/2.21  %Foreground operators:
% 6.40/2.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.40/2.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.40/2.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.40/2.21  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.40/2.21  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.40/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.40/2.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.40/2.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.40/2.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.40/2.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.40/2.21  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 6.40/2.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.40/2.21  tff('#skF_2', type, '#skF_2': $i).
% 6.40/2.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.40/2.21  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.40/2.21  tff('#skF_3', type, '#skF_3': $i).
% 6.40/2.21  tff('#skF_1', type, '#skF_1': $i).
% 6.40/2.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.40/2.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.40/2.21  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.40/2.21  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.40/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.40/2.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.40/2.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.40/2.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.40/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.40/2.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.40/2.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.40/2.21  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.40/2.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.40/2.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.40/2.21  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 6.40/2.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.40/2.21  
% 6.40/2.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.40/2.24  tff(f_286, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 6.40/2.24  tff(f_238, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 6.40/2.24  tff(f_154, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.40/2.24  tff(f_252, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.40/2.24  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.40/2.24  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.40/2.24  tff(f_150, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.40/2.24  tff(f_176, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 6.40/2.24  tff(f_168, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 6.40/2.24  tff(f_192, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 6.40/2.24  tff(f_65, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 6.40/2.24  tff(f_224, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 6.40/2.24  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.40/2.24  tff(f_208, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 6.40/2.24  tff(f_178, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.40/2.24  tff(f_77, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.40/2.24  tff(f_117, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 6.40/2.24  tff(f_127, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 6.40/2.24  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 6.40/2.24  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.40/2.24  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 6.40/2.24  tff(f_144, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 6.40/2.24  tff(f_234, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 6.40/2.24  tff(f_264, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 6.40/2.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.40/2.24  tff(c_110, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_286])).
% 6.40/2.24  tff(c_116, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_286])).
% 6.40/2.24  tff(c_162, plain, (![A_71]: (u1_struct_0(A_71)=k2_struct_0(A_71) | ~l1_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_238])).
% 6.40/2.24  tff(c_170, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_116, c_162])).
% 6.40/2.24  tff(c_112, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_286])).
% 6.40/2.24  tff(c_169, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_112, c_162])).
% 6.40/2.24  tff(c_106, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_286])).
% 6.40/2.24  tff(c_180, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_169, c_106])).
% 6.40/2.24  tff(c_482, plain, (![A_117, B_118, C_119]: (k2_relset_1(A_117, B_118, C_119)=k2_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.40/2.24  tff(c_492, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_180, c_482])).
% 6.40/2.24  tff(c_104, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_286])).
% 6.40/2.24  tff(c_214, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_169, c_104])).
% 6.40/2.24  tff(c_493, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_492, c_214])).
% 6.40/2.24  tff(c_114, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_286])).
% 6.40/2.24  tff(c_182, plain, (![A_72]: (~v1_xboole_0(u1_struct_0(A_72)) | ~l1_struct_0(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_252])).
% 6.40/2.24  tff(c_188, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_169, c_182])).
% 6.40/2.24  tff(c_192, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_188])).
% 6.40/2.24  tff(c_193, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_114, c_192])).
% 6.40/2.24  tff(c_501, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_493, c_193])).
% 6.40/2.24  tff(c_24, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.40/2.24  tff(c_219, plain, (![B_76, A_77]: (v1_relat_1(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_77)) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.40/2.24  tff(c_222, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_180, c_219])).
% 6.40/2.24  tff(c_225, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_222])).
% 6.40/2.24  tff(c_354, plain, (![C_95, A_96, B_97]: (v4_relat_1(C_95, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.40/2.24  tff(c_364, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_180, c_354])).
% 6.40/2.24  tff(c_469, plain, (![B_115, A_116]: (k1_relat_1(B_115)=A_116 | ~v1_partfun1(B_115, A_116) | ~v4_relat_1(B_115, A_116) | ~v1_relat_1(B_115))), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.40/2.24  tff(c_472, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_364, c_469])).
% 6.40/2.24  tff(c_478, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_472])).
% 6.40/2.24  tff(c_481, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_478])).
% 6.40/2.24  tff(c_108, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_286])).
% 6.40/2.24  tff(c_171, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_108])).
% 6.40/2.24  tff(c_181, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_171])).
% 6.40/2.24  tff(c_502, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_493, c_181])).
% 6.40/2.24  tff(c_503, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_493, c_180])).
% 6.40/2.24  tff(c_602, plain, (![C_127, A_128, B_129]: (v1_partfun1(C_127, A_128) | ~v1_funct_2(C_127, A_128, B_129) | ~v1_funct_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | v1_xboole_0(B_129))), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.40/2.24  tff(c_605, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_503, c_602])).
% 6.40/2.24  tff(c_617, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_502, c_605])).
% 6.40/2.24  tff(c_619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_501, c_481, c_617])).
% 6.40/2.24  tff(c_620, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_478])).
% 6.40/2.24  tff(c_627, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_620, c_180])).
% 6.40/2.24  tff(c_723, plain, (![A_133, B_134, C_135]: (k2_relset_1(A_133, B_134, C_135)=k2_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.40/2.24  tff(c_737, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_627, c_723])).
% 6.40/2.24  tff(c_624, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_620, c_214])).
% 6.40/2.24  tff(c_738, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_737, c_624])).
% 6.40/2.24  tff(c_626, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_620, c_181])).
% 6.40/2.24  tff(c_745, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_738, c_626])).
% 6.40/2.24  tff(c_746, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_738, c_627])).
% 6.40/2.24  tff(c_1744, plain, (![A_216, B_217, C_218, D_219]: (r2_funct_2(A_216, B_217, C_218, C_218) | ~m1_subset_1(D_219, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))) | ~v1_funct_2(D_219, A_216, B_217) | ~v1_funct_1(D_219) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))) | ~v1_funct_2(C_218, A_216, B_217) | ~v1_funct_1(C_218))), inference(cnfTransformation, [status(thm)], [f_192])).
% 6.40/2.24  tff(c_1748, plain, (![C_218]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_218, C_218) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_218, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_218))), inference(resolution, [status(thm)], [c_746, c_1744])).
% 6.40/2.24  tff(c_1813, plain, (![C_222]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_222, C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_222, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_222))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_745, c_1748])).
% 6.40/2.24  tff(c_1818, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_746, c_1813])).
% 6.40/2.24  tff(c_1825, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_745, c_1818])).
% 6.40/2.24  tff(c_226, plain, (![A_78]: (k2_relat_1(A_78)=k1_xboole_0 | k1_relat_1(A_78)!=k1_xboole_0 | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.40/2.24  tff(c_242, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_225, c_226])).
% 6.40/2.24  tff(c_271, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_242])).
% 6.40/2.24  tff(c_273, plain, (![A_82]: (k1_relat_1(A_82)=k1_xboole_0 | k2_relat_1(A_82)!=k1_xboole_0 | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.40/2.24  tff(c_276, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_225, c_273])).
% 6.40/2.24  tff(c_291, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_271, c_276])).
% 6.40/2.24  tff(c_743, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_738, c_737])).
% 6.40/2.24  tff(c_102, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_286])).
% 6.40/2.24  tff(c_1428, plain, (![A_210, C_211, B_212]: (k6_partfun1(A_210)=k5_relat_1(C_211, k2_funct_1(C_211)) | k1_xboole_0=B_212 | ~v2_funct_1(C_211) | k2_relset_1(A_210, B_212, C_211)!=B_212 | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_210, B_212))) | ~v1_funct_2(C_211, A_210, B_212) | ~v1_funct_1(C_211))), inference(cnfTransformation, [status(thm)], [f_224])).
% 6.40/2.24  tff(c_1432, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_746, c_1428])).
% 6.40/2.24  tff(c_1442, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_110, c_745, c_743, c_102, c_1432])).
% 6.40/2.24  tff(c_1443, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_291, c_1442])).
% 6.40/2.24  tff(c_34, plain, (![A_15]: (v1_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.40/2.24  tff(c_1042, plain, (![C_167, A_168, B_169]: (v1_funct_1(k2_funct_1(C_167)) | k2_relset_1(A_168, B_169, C_167)!=B_169 | ~v2_funct_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~v1_funct_2(C_167, A_168, B_169) | ~v1_funct_1(C_167))), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.40/2.24  tff(c_1045, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_746, c_1042])).
% 6.40/2.24  tff(c_1057, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_745, c_102, c_743, c_1045])).
% 6.40/2.24  tff(c_72, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.40/2.24  tff(c_38, plain, (![A_16]: (v2_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.40/2.24  tff(c_118, plain, (![A_16]: (v2_funct_1(k6_partfun1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_38])).
% 6.40/2.24  tff(c_48, plain, (![A_21, B_23]: (v2_funct_1(A_21) | k2_relat_1(B_23)!=k1_relat_1(A_21) | ~v2_funct_1(k5_relat_1(B_23, A_21)) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.40/2.24  tff(c_1449, plain, (v2_funct_1(k2_funct_1('#skF_3')) | k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v2_funct_1(k6_partfun1(k1_relat_1('#skF_3'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1443, c_48])).
% 6.40/2.24  tff(c_1456, plain, (v2_funct_1(k2_funct_1('#skF_3')) | k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_225, c_110, c_118, c_1449])).
% 6.40/2.24  tff(c_1460, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1456])).
% 6.40/2.24  tff(c_1463, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_1460])).
% 6.40/2.24  tff(c_1467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_225, c_110, c_1463])).
% 6.40/2.24  tff(c_1469, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1456])).
% 6.40/2.24  tff(c_54, plain, (![A_24]: (k1_relat_1(k2_funct_1(A_24))=k2_relat_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.40/2.24  tff(c_1468, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1456])).
% 6.40/2.24  tff(c_1478, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1468])).
% 6.40/2.24  tff(c_1481, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_54, c_1478])).
% 6.40/2.24  tff(c_1485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_225, c_110, c_102, c_1481])).
% 6.40/2.24  tff(c_1486, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1468])).
% 6.40/2.24  tff(c_1487, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1468])).
% 6.40/2.24  tff(c_26, plain, (![A_13]: (k9_relat_1(A_13, k1_relat_1(A_13))=k2_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.40/2.24  tff(c_1523, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1487, c_26])).
% 6.40/2.24  tff(c_1553, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1469, c_1523])).
% 6.40/2.24  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.40/2.24  tff(c_770, plain, (![A_136, B_137]: (k9_relat_1(k2_funct_1(A_136), k9_relat_1(A_136, B_137))=B_137 | ~r1_tarski(B_137, k1_relat_1(A_136)) | ~v2_funct_1(A_136) | ~v1_funct_1(A_136) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.40/2.24  tff(c_785, plain, (![A_13]: (k9_relat_1(k2_funct_1(A_13), k2_relat_1(A_13))=k1_relat_1(A_13) | ~r1_tarski(k1_relat_1(A_13), k1_relat_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_26, c_770])).
% 6.40/2.24  tff(c_789, plain, (![A_13]: (k9_relat_1(k2_funct_1(A_13), k2_relat_1(A_13))=k1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_785])).
% 6.40/2.24  tff(c_1611, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1553, c_789])).
% 6.40/2.24  tff(c_1621, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_225, c_110, c_102, c_1611])).
% 6.40/2.24  tff(c_56, plain, (![A_25, B_27]: (k2_funct_1(A_25)=B_27 | k6_relat_1(k2_relat_1(A_25))!=k5_relat_1(B_27, A_25) | k2_relat_1(B_27)!=k1_relat_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.40/2.24  tff(c_117, plain, (![A_25, B_27]: (k2_funct_1(A_25)=B_27 | k6_partfun1(k2_relat_1(A_25))!=k5_relat_1(B_27, A_25) | k2_relat_1(B_27)!=k1_relat_1(A_25) | ~v2_funct_1(A_25) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_56])).
% 6.40/2.24  tff(c_1647, plain, (![B_27]: (k2_funct_1(k2_funct_1('#skF_3'))=B_27 | k5_relat_1(B_27, k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3')) | k2_relat_1(B_27)!=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1621, c_117])).
% 6.40/2.24  tff(c_3868, plain, (![B_286]: (k2_funct_1(k2_funct_1('#skF_3'))=B_286 | k5_relat_1(B_286, k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3')) | k2_relat_1(B_286)!=k2_relat_1('#skF_3') | ~v1_funct_1(B_286) | ~v1_relat_1(B_286))), inference(demodulation, [status(thm), theory('equality')], [c_1469, c_1057, c_1486, c_1487, c_1647])).
% 6.40/2.24  tff(c_3874, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1443, c_3868])).
% 6.40/2.24  tff(c_3881, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_225, c_110, c_3874])).
% 6.40/2.24  tff(c_1155, plain, (![C_187, B_188, A_189]: (v1_funct_2(k2_funct_1(C_187), B_188, A_189) | k2_relset_1(A_189, B_188, C_187)!=B_188 | ~v2_funct_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_189, B_188))) | ~v1_funct_2(C_187, A_189, B_188) | ~v1_funct_1(C_187))), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.40/2.24  tff(c_1158, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_746, c_1155])).
% 6.40/2.24  tff(c_1170, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_745, c_102, c_743, c_1158])).
% 6.40/2.24  tff(c_86, plain, (![A_51]: (m1_subset_1(A_51, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_51), k2_relat_1(A_51)))) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_234])).
% 6.40/2.24  tff(c_736, plain, (![A_51]: (k2_relset_1(k1_relat_1(A_51), k2_relat_1(A_51), A_51)=k2_relat_1(A_51) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(resolution, [status(thm)], [c_86, c_723])).
% 6.40/2.24  tff(c_1665, plain, (k2_relset_1(k1_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1621, c_736])).
% 6.40/2.24  tff(c_1703, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1469, c_1057, c_1621, c_1487, c_1665])).
% 6.40/2.24  tff(c_1671, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1621, c_86])).
% 6.40/2.24  tff(c_1707, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1469, c_1057, c_1487, c_1671])).
% 6.40/2.24  tff(c_98, plain, (![A_55, B_56, C_57]: (k2_tops_2(A_55, B_56, C_57)=k2_funct_1(C_57) | ~v2_funct_1(C_57) | k2_relset_1(A_55, B_56, C_57)!=B_56 | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))) | ~v1_funct_2(C_57, A_55, B_56) | ~v1_funct_1(C_57))), inference(cnfTransformation, [status(thm)], [f_264])).
% 6.40/2.24  tff(c_1901, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1707, c_98])).
% 6.40/2.24  tff(c_1936, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_1170, c_1703, c_1486, c_1901])).
% 6.40/2.24  tff(c_1214, plain, (![A_195, B_196, C_197]: (k2_tops_2(A_195, B_196, C_197)=k2_funct_1(C_197) | ~v2_funct_1(C_197) | k2_relset_1(A_195, B_196, C_197)!=B_196 | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))) | ~v1_funct_2(C_197, A_195, B_196) | ~v1_funct_1(C_197))), inference(cnfTransformation, [status(thm)], [f_264])).
% 6.40/2.24  tff(c_1217, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_746, c_1214])).
% 6.40/2.24  tff(c_1229, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_745, c_743, c_102, c_1217])).
% 6.40/2.24  tff(c_100, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_286])).
% 6.40/2.24  tff(c_272, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_170, c_170, c_169, c_169, c_169, c_100])).
% 6.40/2.24  tff(c_623, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_620, c_620, c_620, c_272])).
% 6.40/2.24  tff(c_744, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_738, c_738, c_738, c_623])).
% 6.40/2.24  tff(c_1231, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1229, c_744])).
% 6.40/2.24  tff(c_2307, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1936, c_1231])).
% 6.40/2.24  tff(c_3899, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3881, c_2307])).
% 6.40/2.24  tff(c_3921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1825, c_3899])).
% 6.40/2.24  tff(c_3922, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_242])).
% 6.40/2.24  tff(c_4270, plain, (![A_327, B_328, C_329]: (k2_relset_1(A_327, B_328, C_329)=k2_relat_1(C_329) | ~m1_subset_1(C_329, k1_zfmisc_1(k2_zfmisc_1(A_327, B_328))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.40/2.24  tff(c_4276, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_180, c_4270])).
% 6.40/2.24  tff(c_4285, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3922, c_4276])).
% 6.40/2.24  tff(c_4289, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4285, c_214])).
% 6.40/2.24  tff(c_4296, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4289, c_193])).
% 6.40/2.24  tff(c_4302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_4296])).
% 6.40/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.40/2.24  
% 6.40/2.24  Inference rules
% 6.40/2.24  ----------------------
% 6.40/2.24  #Ref     : 0
% 6.40/2.24  #Sup     : 870
% 6.40/2.24  #Fact    : 0
% 6.40/2.24  #Define  : 0
% 6.40/2.24  #Split   : 12
% 6.40/2.24  #Chain   : 0
% 6.40/2.24  #Close   : 0
% 6.40/2.24  
% 6.40/2.24  Ordering : KBO
% 6.40/2.24  
% 6.40/2.24  Simplification rules
% 6.40/2.24  ----------------------
% 6.40/2.24  #Subsume      : 167
% 6.40/2.24  #Demod        : 1616
% 6.40/2.24  #Tautology    : 360
% 6.40/2.24  #SimpNegUnit  : 56
% 6.40/2.24  #BackRed      : 66
% 6.40/2.24  
% 6.40/2.24  #Partial instantiations: 0
% 6.40/2.24  #Strategies tried      : 1
% 6.40/2.24  
% 6.40/2.24  Timing (in seconds)
% 6.40/2.24  ----------------------
% 6.40/2.24  Preprocessing        : 0.39
% 6.40/2.24  Parsing              : 0.21
% 6.40/2.24  CNF conversion       : 0.03
% 6.40/2.24  Main loop            : 1.04
% 6.40/2.24  Inferencing          : 0.33
% 6.40/2.24  Reduction            : 0.39
% 6.40/2.24  Demodulation         : 0.29
% 6.40/2.24  BG Simplification    : 0.04
% 6.40/2.24  Subsumption          : 0.20
% 6.40/2.24  Abstraction          : 0.04
% 6.40/2.24  MUC search           : 0.00
% 6.40/2.24  Cooper               : 0.00
% 6.40/2.24  Total                : 1.48
% 6.40/2.24  Index Insertion      : 0.00
% 6.40/2.24  Index Deletion       : 0.00
% 6.40/2.24  Index Matching       : 0.00
% 6.40/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
