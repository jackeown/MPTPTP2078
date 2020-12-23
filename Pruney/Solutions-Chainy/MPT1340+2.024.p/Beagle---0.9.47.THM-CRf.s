%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:33 EST 2020

% Result     : Theorem 5.90s
% Output     : CNFRefutation 5.90s
% Verified   : 
% Statistics : Number of formulae       :  153 (24089 expanded)
%              Number of leaves         :   45 (8654 expanded)
%              Depth                    :   25
%              Number of atoms          :  351 (73622 expanded)
%              Number of equality atoms :   99 (18937 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_188,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_146,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_142,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_100,axiom,(
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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_154,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_166,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_80,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_81,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_89,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_81])).

tff(c_76,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_88,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_81])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_120,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_88,c_70])).

tff(c_20,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_124,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_20])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_66,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_54,plain,(
    ! [A_28] :
      ( v1_funct_2(A_28,k1_relat_1(A_28),k2_relat_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_52,plain,(
    ! [A_28] :
      ( m1_subset_1(A_28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_28),k2_relat_1(A_28))))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_327,plain,(
    ! [B_78,A_79,C_80] :
      ( k1_xboole_0 = B_78
      | k1_relset_1(A_79,B_78,C_80) = A_79
      | ~ v1_funct_2(C_80,A_79,B_78)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_545,plain,(
    ! [A_102] :
      ( k2_relat_1(A_102) = k1_xboole_0
      | k1_relset_1(k1_relat_1(A_102),k2_relat_1(A_102),A_102) = k1_relat_1(A_102)
      | ~ v1_funct_2(A_102,k1_relat_1(A_102),k2_relat_1(A_102))
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(resolution,[status(thm)],[c_52,c_327])).

tff(c_556,plain,(
    ! [A_103] :
      ( k2_relat_1(A_103) = k1_xboole_0
      | k1_relset_1(k1_relat_1(A_103),k2_relat_1(A_103),A_103) = k1_relat_1(A_103)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(resolution,[status(thm)],[c_54,c_545])).

tff(c_303,plain,(
    ! [A_68,B_69,C_70] :
      ( k8_relset_1(A_68,B_69,C_70,B_69) = k1_relset_1(A_68,B_69,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_386,plain,(
    ! [A_91] :
      ( k8_relset_1(k1_relat_1(A_91),k2_relat_1(A_91),A_91,k2_relat_1(A_91)) = k1_relset_1(k1_relat_1(A_91),k2_relat_1(A_91),A_91)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(resolution,[status(thm)],[c_52,c_303])).

tff(c_259,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( k8_relset_1(A_56,B_57,C_58,D_59) = k10_relat_1(C_58,D_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_265,plain,(
    ! [A_28,D_59] :
      ( k8_relset_1(k1_relat_1(A_28),k2_relat_1(A_28),A_28,D_59) = k10_relat_1(A_28,D_59)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(resolution,[status(thm)],[c_52,c_259])).

tff(c_392,plain,(
    ! [A_91] :
      ( k1_relset_1(k1_relat_1(A_91),k2_relat_1(A_91),A_91) = k10_relat_1(A_91,k2_relat_1(A_91))
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_265])).

tff(c_577,plain,(
    ! [A_104] :
      ( k10_relat_1(A_104,k2_relat_1(A_104)) = k1_relat_1(A_104)
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104)
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104)
      | k2_relat_1(A_104) = k1_xboole_0
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_392])).

tff(c_195,plain,(
    ! [A_51,B_52,C_53] :
      ( k2_relset_1(A_51,B_52,C_53) = k2_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_203,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_195])).

tff(c_68,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_115,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_88,c_68])).

tff(c_204,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_115])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_98,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_88,c_72])).

tff(c_213,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_98])).

tff(c_211,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_120])).

tff(c_264,plain,(
    ! [D_59] : k8_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3',D_59) = k10_relat_1('#skF_3',D_59) ),
    inference(resolution,[status(thm)],[c_211,c_259])).

tff(c_305,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3',k2_relat_1('#skF_3')) = k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_211,c_303])).

tff(c_309,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k10_relat_1('#skF_3',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_305])).

tff(c_330,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_211,c_327])).

tff(c_336,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_309,c_330])).

tff(c_338,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_583,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_338])).

tff(c_595,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_74,c_124,c_74,c_124,c_74,c_583])).

tff(c_610,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_595])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_99,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(u1_struct_0(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_105,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_99])).

tff(c_109,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_105])).

tff(c_110,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_109])).

tff(c_212,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_110])).

tff(c_623,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_212])).

tff(c_627,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_623])).

tff(c_629,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_595])).

tff(c_589,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_577])).

tff(c_598,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_74,c_124,c_74,c_124,c_74,c_589])).

tff(c_630,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_629,c_598])).

tff(c_348,plain,(
    ! [A_81,B_82,D_83] :
      ( r2_funct_2(A_81,B_82,D_83,D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ v1_funct_2(D_83,A_81,B_82)
      | ~ v1_funct_1(D_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_350,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_211,c_348])).

tff(c_355,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_213,c_350])).

tff(c_634,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_355])).

tff(c_18,plain,(
    ! [A_4] :
      ( k2_funct_1(k2_funct_1(A_4)) = A_4
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_641,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_213])).

tff(c_209,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_203])).

tff(c_639,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_209])).

tff(c_357,plain,(
    ! [C_84,A_85,B_86] :
      ( v1_funct_1(k2_funct_1(C_84))
      | k2_relset_1(A_85,B_86,C_84) != B_86
      | ~ v2_funct_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ v1_funct_2(C_84,A_85,B_86)
      | ~ v1_funct_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_360,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_211,c_357])).

tff(c_366,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_213,c_66,c_209,c_360])).

tff(c_375,plain,(
    ! [C_88,B_89,A_90] :
      ( v1_funct_2(k2_funct_1(C_88),B_89,A_90)
      | k2_relset_1(A_90,B_89,C_88) != B_89
      | ~ v2_funct_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89)))
      | ~ v1_funct_2(C_88,A_90,B_89)
      | ~ v1_funct_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_378,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_211,c_375])).

tff(c_384,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_213,c_66,c_209,c_378])).

tff(c_633,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_384])).

tff(c_14,plain,(
    ! [A_3] :
      ( k2_relat_1(k2_funct_1(A_3)) = k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_2] :
      ( v2_funct_1(k2_funct_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_640,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_211])).

tff(c_460,plain,(
    ! [C_97,B_98,A_99] :
      ( m1_subset_1(k2_funct_1(C_97),k1_zfmisc_1(k2_zfmisc_1(B_98,A_99)))
      | k2_relset_1(A_99,B_98,C_97) != B_98
      | ~ v2_funct_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98)))
      | ~ v1_funct_2(C_97,A_99,B_98)
      | ~ v1_funct_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_22,plain,(
    ! [A_8,B_9,C_10] :
      ( k2_relset_1(A_8,B_9,C_10) = k2_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_968,plain,(
    ! [B_115,A_116,C_117] :
      ( k2_relset_1(B_115,A_116,k2_funct_1(C_117)) = k2_relat_1(k2_funct_1(C_117))
      | k2_relset_1(A_116,B_115,C_117) != B_115
      | ~ v2_funct_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115)))
      | ~ v1_funct_2(C_117,A_116,B_115)
      | ~ v1_funct_1(C_117) ) ),
    inference(resolution,[status(thm)],[c_460,c_22])).

tff(c_974,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_640,c_968])).

tff(c_987,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_641,c_66,c_639,c_974])).

tff(c_50,plain,(
    ! [C_27,A_25,B_26] :
      ( v1_funct_1(k2_funct_1(C_27))
      | k2_relset_1(A_25,B_26,C_27) != B_26
      | ~ v2_funct_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_2(C_27,A_25,B_26)
      | ~ v1_funct_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2274,plain,(
    ! [C_188,B_189,A_190] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_188)))
      | k2_relset_1(B_189,A_190,k2_funct_1(C_188)) != A_190
      | ~ v2_funct_1(k2_funct_1(C_188))
      | ~ v1_funct_2(k2_funct_1(C_188),B_189,A_190)
      | ~ v1_funct_1(k2_funct_1(C_188))
      | k2_relset_1(A_190,B_189,C_188) != B_189
      | ~ v2_funct_1(C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_190,B_189)))
      | ~ v1_funct_2(C_188,A_190,B_189)
      | ~ v1_funct_1(C_188) ) ),
    inference(resolution,[status(thm)],[c_460,c_50])).

tff(c_2283,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_640,c_2274])).

tff(c_2297,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_641,c_66,c_639,c_366,c_633,c_987,c_2283])).

tff(c_2640,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2297])).

tff(c_2643,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_2640])).

tff(c_2647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_74,c_66,c_2643])).

tff(c_2648,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2297])).

tff(c_3002,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2648])).

tff(c_3005,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3002])).

tff(c_3009,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_74,c_66,c_3005])).

tff(c_3011,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2648])).

tff(c_3021,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3011,c_987])).

tff(c_2649,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2297])).

tff(c_62,plain,(
    ! [A_31,B_32,C_33] :
      ( k2_tops_2(A_31,B_32,C_33) = k2_funct_1(C_33)
      | ~ v2_funct_1(C_33)
      | k2_relset_1(A_31,B_32,C_33) != B_32
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_2(C_33,A_31,B_32)
      | ~ v1_funct_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_3375,plain,(
    ! [B_194,A_195,C_196] :
      ( k2_tops_2(B_194,A_195,k2_funct_1(C_196)) = k2_funct_1(k2_funct_1(C_196))
      | ~ v2_funct_1(k2_funct_1(C_196))
      | k2_relset_1(B_194,A_195,k2_funct_1(C_196)) != A_195
      | ~ v1_funct_2(k2_funct_1(C_196),B_194,A_195)
      | ~ v1_funct_1(k2_funct_1(C_196))
      | k2_relset_1(A_195,B_194,C_196) != B_194
      | ~ v2_funct_1(C_196)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_195,B_194)))
      | ~ v1_funct_2(C_196,A_195,B_194)
      | ~ v1_funct_1(C_196) ) ),
    inference(resolution,[status(thm)],[c_460,c_62])).

tff(c_3384,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_640,c_3375])).

tff(c_3398,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_641,c_66,c_639,c_366,c_633,c_3021,c_2649,c_3384])).

tff(c_444,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_tops_2(A_94,B_95,C_96) = k2_funct_1(C_96)
      | ~ v2_funct_1(C_96)
      | k2_relset_1(A_94,B_95,C_96) != B_95
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_2(C_96,A_94,B_95)
      | ~ v1_funct_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_447,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_211,c_444])).

tff(c_453,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_213,c_209,c_66,c_447])).

tff(c_64,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_125,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_89,c_89,c_88,c_88,c_88,c_64])).

tff(c_210,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_204,c_204,c_125])).

tff(c_455,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_210])).

tff(c_631,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_630,c_455])).

tff(c_3523,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3398,c_631])).

tff(c_3530,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3523])).

tff(c_3533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_74,c_66,c_634,c_3530])).

tff(c_3534,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_3544,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3534,c_212])).

tff(c_3548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3544])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:38:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.90/2.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.90/2.15  
% 5.90/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.90/2.15  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.90/2.15  
% 5.90/2.15  %Foreground sorts:
% 5.90/2.15  
% 5.90/2.15  
% 5.90/2.15  %Background operators:
% 5.90/2.15  
% 5.90/2.15  
% 5.90/2.15  %Foreground operators:
% 5.90/2.15  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.90/2.15  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.90/2.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.90/2.15  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.90/2.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.90/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.90/2.15  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.90/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.90/2.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.90/2.15  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 5.90/2.15  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.90/2.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.90/2.15  tff('#skF_2', type, '#skF_2': $i).
% 5.90/2.15  tff('#skF_3', type, '#skF_3': $i).
% 5.90/2.15  tff('#skF_1', type, '#skF_1': $i).
% 5.90/2.15  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.90/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.90/2.15  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.90/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.90/2.15  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.90/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.90/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.90/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.90/2.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.90/2.15  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.90/2.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.90/2.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.90/2.15  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 5.90/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.90/2.15  
% 5.90/2.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.90/2.17  tff(f_188, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 5.90/2.17  tff(f_146, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.90/2.17  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.90/2.17  tff(f_142, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 5.90/2.17  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.90/2.17  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 5.90/2.17  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 5.90/2.17  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.90/2.17  tff(f_154, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.90/2.17  tff(f_116, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 5.90/2.17  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 5.90/2.17  tff(f_132, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 5.90/2.17  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 5.90/2.17  tff(f_46, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 5.90/2.17  tff(f_166, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 5.90/2.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.90/2.17  tff(c_80, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.90/2.17  tff(c_81, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.90/2.17  tff(c_89, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_80, c_81])).
% 5.90/2.17  tff(c_76, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.90/2.17  tff(c_88, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_81])).
% 5.90/2.17  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.90/2.17  tff(c_120, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_88, c_70])).
% 5.90/2.17  tff(c_20, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.90/2.17  tff(c_124, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_120, c_20])).
% 5.90/2.17  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.90/2.17  tff(c_66, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.90/2.17  tff(c_54, plain, (![A_28]: (v1_funct_2(A_28, k1_relat_1(A_28), k2_relat_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.90/2.17  tff(c_52, plain, (![A_28]: (m1_subset_1(A_28, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_28), k2_relat_1(A_28)))) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.90/2.17  tff(c_327, plain, (![B_78, A_79, C_80]: (k1_xboole_0=B_78 | k1_relset_1(A_79, B_78, C_80)=A_79 | ~v1_funct_2(C_80, A_79, B_78) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.90/2.17  tff(c_545, plain, (![A_102]: (k2_relat_1(A_102)=k1_xboole_0 | k1_relset_1(k1_relat_1(A_102), k2_relat_1(A_102), A_102)=k1_relat_1(A_102) | ~v1_funct_2(A_102, k1_relat_1(A_102), k2_relat_1(A_102)) | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(resolution, [status(thm)], [c_52, c_327])).
% 5.90/2.17  tff(c_556, plain, (![A_103]: (k2_relat_1(A_103)=k1_xboole_0 | k1_relset_1(k1_relat_1(A_103), k2_relat_1(A_103), A_103)=k1_relat_1(A_103) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(resolution, [status(thm)], [c_54, c_545])).
% 5.90/2.17  tff(c_303, plain, (![A_68, B_69, C_70]: (k8_relset_1(A_68, B_69, C_70, B_69)=k1_relset_1(A_68, B_69, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.90/2.17  tff(c_386, plain, (![A_91]: (k8_relset_1(k1_relat_1(A_91), k2_relat_1(A_91), A_91, k2_relat_1(A_91))=k1_relset_1(k1_relat_1(A_91), k2_relat_1(A_91), A_91) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(resolution, [status(thm)], [c_52, c_303])).
% 5.90/2.17  tff(c_259, plain, (![A_56, B_57, C_58, D_59]: (k8_relset_1(A_56, B_57, C_58, D_59)=k10_relat_1(C_58, D_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.90/2.17  tff(c_265, plain, (![A_28, D_59]: (k8_relset_1(k1_relat_1(A_28), k2_relat_1(A_28), A_28, D_59)=k10_relat_1(A_28, D_59) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(resolution, [status(thm)], [c_52, c_259])).
% 5.90/2.17  tff(c_392, plain, (![A_91]: (k1_relset_1(k1_relat_1(A_91), k2_relat_1(A_91), A_91)=k10_relat_1(A_91, k2_relat_1(A_91)) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(superposition, [status(thm), theory('equality')], [c_386, c_265])).
% 5.90/2.17  tff(c_577, plain, (![A_104]: (k10_relat_1(A_104, k2_relat_1(A_104))=k1_relat_1(A_104) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104) | k2_relat_1(A_104)=k1_xboole_0 | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(superposition, [status(thm), theory('equality')], [c_556, c_392])).
% 5.90/2.17  tff(c_195, plain, (![A_51, B_52, C_53]: (k2_relset_1(A_51, B_52, C_53)=k2_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.90/2.17  tff(c_203, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_120, c_195])).
% 5.90/2.17  tff(c_68, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.90/2.17  tff(c_115, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_88, c_68])).
% 5.90/2.17  tff(c_204, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_115])).
% 5.90/2.17  tff(c_72, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.90/2.18  tff(c_98, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_88, c_72])).
% 5.90/2.18  tff(c_213, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_98])).
% 5.90/2.18  tff(c_211, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_120])).
% 5.90/2.18  tff(c_264, plain, (![D_59]: (k8_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', D_59)=k10_relat_1('#skF_3', D_59))), inference(resolution, [status(thm)], [c_211, c_259])).
% 5.90/2.18  tff(c_305, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', k2_relat_1('#skF_3'))=k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_211, c_303])).
% 5.90/2.18  tff(c_309, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k10_relat_1('#skF_3', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_305])).
% 5.90/2.18  tff(c_330, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_211, c_327])).
% 5.90/2.18  tff(c_336, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_309, c_330])).
% 5.90/2.18  tff(c_338, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_336])).
% 5.90/2.18  tff(c_583, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k2_relat_1('#skF_3')=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_577, c_338])).
% 5.90/2.18  tff(c_595, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_124, c_74, c_124, c_74, c_124, c_74, c_583])).
% 5.90/2.18  tff(c_610, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_595])).
% 5.90/2.18  tff(c_78, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.90/2.18  tff(c_99, plain, (![A_39]: (~v1_xboole_0(u1_struct_0(A_39)) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.90/2.18  tff(c_105, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_88, c_99])).
% 5.90/2.18  tff(c_109, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_105])).
% 5.90/2.18  tff(c_110, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_78, c_109])).
% 5.90/2.18  tff(c_212, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_110])).
% 5.90/2.18  tff(c_623, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_610, c_212])).
% 5.90/2.18  tff(c_627, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_623])).
% 5.90/2.18  tff(c_629, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_595])).
% 5.90/2.18  tff(c_589, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k2_relat_1('#skF_3')=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_338, c_577])).
% 5.90/2.18  tff(c_598, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_124, c_74, c_124, c_74, c_124, c_74, c_589])).
% 5.90/2.18  tff(c_630, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_629, c_598])).
% 5.90/2.18  tff(c_348, plain, (![A_81, B_82, D_83]: (r2_funct_2(A_81, B_82, D_83, D_83) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~v1_funct_2(D_83, A_81, B_82) | ~v1_funct_1(D_83))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.90/2.18  tff(c_350, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_211, c_348])).
% 5.90/2.18  tff(c_355, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_213, c_350])).
% 5.90/2.18  tff(c_634, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_630, c_355])).
% 5.90/2.18  tff(c_18, plain, (![A_4]: (k2_funct_1(k2_funct_1(A_4))=A_4 | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.90/2.18  tff(c_641, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_630, c_213])).
% 5.90/2.18  tff(c_209, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_203])).
% 5.90/2.18  tff(c_639, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_630, c_209])).
% 5.90/2.18  tff(c_357, plain, (![C_84, A_85, B_86]: (v1_funct_1(k2_funct_1(C_84)) | k2_relset_1(A_85, B_86, C_84)!=B_86 | ~v2_funct_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~v1_funct_2(C_84, A_85, B_86) | ~v1_funct_1(C_84))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.90/2.18  tff(c_360, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_211, c_357])).
% 5.90/2.18  tff(c_366, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_213, c_66, c_209, c_360])).
% 5.90/2.18  tff(c_375, plain, (![C_88, B_89, A_90]: (v1_funct_2(k2_funct_1(C_88), B_89, A_90) | k2_relset_1(A_90, B_89, C_88)!=B_89 | ~v2_funct_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))) | ~v1_funct_2(C_88, A_90, B_89) | ~v1_funct_1(C_88))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.90/2.18  tff(c_378, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_211, c_375])).
% 5.90/2.18  tff(c_384, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_213, c_66, c_209, c_378])).
% 5.90/2.18  tff(c_633, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_630, c_384])).
% 5.90/2.18  tff(c_14, plain, (![A_3]: (k2_relat_1(k2_funct_1(A_3))=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.90/2.18  tff(c_8, plain, (![A_2]: (v2_funct_1(k2_funct_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.90/2.18  tff(c_640, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_630, c_211])).
% 5.90/2.18  tff(c_460, plain, (![C_97, B_98, A_99]: (m1_subset_1(k2_funct_1(C_97), k1_zfmisc_1(k2_zfmisc_1(B_98, A_99))) | k2_relset_1(A_99, B_98, C_97)!=B_98 | ~v2_funct_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))) | ~v1_funct_2(C_97, A_99, B_98) | ~v1_funct_1(C_97))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.90/2.18  tff(c_22, plain, (![A_8, B_9, C_10]: (k2_relset_1(A_8, B_9, C_10)=k2_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.90/2.18  tff(c_968, plain, (![B_115, A_116, C_117]: (k2_relset_1(B_115, A_116, k2_funct_1(C_117))=k2_relat_1(k2_funct_1(C_117)) | k2_relset_1(A_116, B_115, C_117)!=B_115 | ~v2_funct_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))) | ~v1_funct_2(C_117, A_116, B_115) | ~v1_funct_1(C_117))), inference(resolution, [status(thm)], [c_460, c_22])).
% 5.90/2.18  tff(c_974, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_640, c_968])).
% 5.90/2.18  tff(c_987, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_641, c_66, c_639, c_974])).
% 5.90/2.18  tff(c_50, plain, (![C_27, A_25, B_26]: (v1_funct_1(k2_funct_1(C_27)) | k2_relset_1(A_25, B_26, C_27)!=B_26 | ~v2_funct_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_2(C_27, A_25, B_26) | ~v1_funct_1(C_27))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.90/2.18  tff(c_2274, plain, (![C_188, B_189, A_190]: (v1_funct_1(k2_funct_1(k2_funct_1(C_188))) | k2_relset_1(B_189, A_190, k2_funct_1(C_188))!=A_190 | ~v2_funct_1(k2_funct_1(C_188)) | ~v1_funct_2(k2_funct_1(C_188), B_189, A_190) | ~v1_funct_1(k2_funct_1(C_188)) | k2_relset_1(A_190, B_189, C_188)!=B_189 | ~v2_funct_1(C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_190, B_189))) | ~v1_funct_2(C_188, A_190, B_189) | ~v1_funct_1(C_188))), inference(resolution, [status(thm)], [c_460, c_50])).
% 5.90/2.18  tff(c_2283, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_640, c_2274])).
% 5.90/2.18  tff(c_2297, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_641, c_66, c_639, c_366, c_633, c_987, c_2283])).
% 5.90/2.18  tff(c_2640, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2297])).
% 5.90/2.18  tff(c_2643, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_2640])).
% 5.90/2.18  tff(c_2647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_74, c_66, c_2643])).
% 5.90/2.18  tff(c_2648, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2297])).
% 5.90/2.18  tff(c_3002, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_2648])).
% 5.90/2.18  tff(c_3005, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_3002])).
% 5.90/2.18  tff(c_3009, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_74, c_66, c_3005])).
% 5.90/2.18  tff(c_3011, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_2648])).
% 5.90/2.18  tff(c_3021, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3011, c_987])).
% 5.90/2.18  tff(c_2649, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2297])).
% 5.90/2.18  tff(c_62, plain, (![A_31, B_32, C_33]: (k2_tops_2(A_31, B_32, C_33)=k2_funct_1(C_33) | ~v2_funct_1(C_33) | k2_relset_1(A_31, B_32, C_33)!=B_32 | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_2(C_33, A_31, B_32) | ~v1_funct_1(C_33))), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.90/2.18  tff(c_3375, plain, (![B_194, A_195, C_196]: (k2_tops_2(B_194, A_195, k2_funct_1(C_196))=k2_funct_1(k2_funct_1(C_196)) | ~v2_funct_1(k2_funct_1(C_196)) | k2_relset_1(B_194, A_195, k2_funct_1(C_196))!=A_195 | ~v1_funct_2(k2_funct_1(C_196), B_194, A_195) | ~v1_funct_1(k2_funct_1(C_196)) | k2_relset_1(A_195, B_194, C_196)!=B_194 | ~v2_funct_1(C_196) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_195, B_194))) | ~v1_funct_2(C_196, A_195, B_194) | ~v1_funct_1(C_196))), inference(resolution, [status(thm)], [c_460, c_62])).
% 5.90/2.18  tff(c_3384, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_640, c_3375])).
% 5.90/2.18  tff(c_3398, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_641, c_66, c_639, c_366, c_633, c_3021, c_2649, c_3384])).
% 5.90/2.18  tff(c_444, plain, (![A_94, B_95, C_96]: (k2_tops_2(A_94, B_95, C_96)=k2_funct_1(C_96) | ~v2_funct_1(C_96) | k2_relset_1(A_94, B_95, C_96)!=B_95 | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_2(C_96, A_94, B_95) | ~v1_funct_1(C_96))), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.90/2.18  tff(c_447, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_211, c_444])).
% 5.90/2.18  tff(c_453, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_213, c_209, c_66, c_447])).
% 5.90/2.18  tff(c_64, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.90/2.18  tff(c_125, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_89, c_89, c_88, c_88, c_88, c_64])).
% 5.90/2.18  tff(c_210, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_204, c_204, c_125])).
% 5.90/2.18  tff(c_455, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_453, c_210])).
% 5.90/2.18  tff(c_631, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_630, c_630, c_455])).
% 5.90/2.18  tff(c_3523, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3398, c_631])).
% 5.90/2.18  tff(c_3530, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_3523])).
% 5.90/2.18  tff(c_3533, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_74, c_66, c_634, c_3530])).
% 5.90/2.18  tff(c_3534, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_336])).
% 5.90/2.18  tff(c_3544, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3534, c_212])).
% 5.90/2.18  tff(c_3548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_3544])).
% 5.90/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.90/2.18  
% 5.90/2.18  Inference rules
% 5.90/2.18  ----------------------
% 5.90/2.18  #Ref     : 0
% 5.90/2.18  #Sup     : 824
% 5.90/2.18  #Fact    : 0
% 5.90/2.18  #Define  : 0
% 5.90/2.18  #Split   : 7
% 5.90/2.18  #Chain   : 0
% 5.90/2.18  #Close   : 0
% 5.90/2.18  
% 5.90/2.18  Ordering : KBO
% 5.90/2.18  
% 5.90/2.18  Simplification rules
% 5.90/2.18  ----------------------
% 5.90/2.18  #Subsume      : 51
% 5.90/2.18  #Demod        : 1481
% 5.90/2.18  #Tautology    : 268
% 5.90/2.18  #SimpNegUnit  : 21
% 5.90/2.18  #BackRed      : 72
% 5.90/2.18  
% 5.90/2.18  #Partial instantiations: 0
% 5.90/2.18  #Strategies tried      : 1
% 5.90/2.18  
% 5.90/2.18  Timing (in seconds)
% 5.90/2.18  ----------------------
% 5.90/2.18  Preprocessing        : 0.36
% 5.90/2.18  Parsing              : 0.19
% 5.90/2.18  CNF conversion       : 0.02
% 5.90/2.18  Main loop            : 1.01
% 5.90/2.18  Inferencing          : 0.34
% 5.90/2.18  Reduction            : 0.35
% 5.90/2.18  Demodulation         : 0.26
% 5.90/2.18  BG Simplification    : 0.06
% 5.90/2.18  Subsumption          : 0.19
% 5.90/2.18  Abstraction          : 0.05
% 5.90/2.18  MUC search           : 0.00
% 5.90/2.18  Cooper               : 0.00
% 5.90/2.18  Total                : 1.43
% 5.90/2.18  Index Insertion      : 0.00
% 5.90/2.18  Index Deletion       : 0.00
% 5.90/2.18  Index Matching       : 0.00
% 5.90/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
