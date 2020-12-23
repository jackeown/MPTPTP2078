%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:21 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :  166 (3627 expanded)
%              Number of leaves         :   49 (1324 expanded)
%              Depth                    :   18
%              Number of atoms          :  299 (11200 expanded)
%              Number of equality atoms :  125 (4157 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
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
                 => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                    & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_72,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_64,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_28,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_30,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_92,axiom,(
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

tff(f_132,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_64,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_86,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_94,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_86])).

tff(c_60,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_93,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_86])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_119,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_93,c_54])).

tff(c_125,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_136,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_119,c_125])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_50,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_8,plain,(
    ! [A_3] :
      ( k2_relat_1(k2_funct_1(A_3)) = k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_28,plain,(
    ! [A_18] : k6_relat_1(A_18) = k6_partfun1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    ! [A_14] : m1_subset_1(k6_relat_1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_65,plain,(
    ! [A_14] : m1_subset_1(k6_partfun1(A_14),k1_zfmisc_1(k2_zfmisc_1(A_14,A_14))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22])).

tff(c_780,plain,(
    ! [A_117,B_118,C_119] :
      ( k1_relset_1(A_117,B_118,C_119) = k1_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_792,plain,(
    ! [A_14] : k1_relset_1(A_14,A_14,k6_partfun1(A_14)) = k1_relat_1(k6_partfun1(A_14)) ),
    inference(resolution,[status(thm)],[c_65,c_780])).

tff(c_4,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_66,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_141,plain,(
    ! [A_48,B_49] :
      ( k8_relset_1(A_48,A_48,k6_partfun1(A_48),B_49) = B_49
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_150,plain,(
    ! [A_2] : k8_relset_1(A_2,A_2,k6_partfun1(A_2),A_2) = A_2 ),
    inference(resolution,[status(thm)],[c_66,c_141])).

tff(c_968,plain,(
    ! [A_137,B_138,C_139] :
      ( k8_relset_1(A_137,B_138,C_139,B_138) = k1_relset_1(A_137,B_138,C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_972,plain,(
    ! [A_14] : k8_relset_1(A_14,A_14,k6_partfun1(A_14),A_14) = k1_relset_1(A_14,A_14,k6_partfun1(A_14)) ),
    inference(resolution,[status(thm)],[c_65,c_968])).

tff(c_979,plain,(
    ! [A_14] : k1_relat_1(k6_partfun1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_150,c_972])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_820,plain,(
    ! [A_123,B_124,C_125] :
      ( k2_relset_1(A_123,B_124,C_125) = k2_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_831,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_119,c_820])).

tff(c_52,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_120,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_93,c_52])).

tff(c_843,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_120])).

tff(c_56,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_95,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_56])).

tff(c_104,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95])).

tff(c_853,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_104])).

tff(c_848,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_831])).

tff(c_851,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_119])).

tff(c_1150,plain,(
    ! [A_168,C_169,B_170] :
      ( k6_partfun1(A_168) = k5_relat_1(C_169,k2_funct_1(C_169))
      | k1_xboole_0 = B_170
      | ~ v2_funct_1(C_169)
      | k2_relset_1(A_168,B_170,C_169) != B_170
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_168,B_170)))
      | ~ v1_funct_2(C_169,A_168,B_170)
      | ~ v1_funct_1(C_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1154,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_851,c_1150])).

tff(c_1163,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_853,c_848,c_50,c_1154])).

tff(c_1168,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1163])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_105,plain,(
    ! [A_40] :
      ( ~ v1_xboole_0(u1_struct_0(A_40))
      | ~ l1_struct_0(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_111,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_105])).

tff(c_115,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_111])).

tff(c_116,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_115])).

tff(c_852,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_116])).

tff(c_1181,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1168,c_852])).

tff(c_1185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1181])).

tff(c_1186,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1163])).

tff(c_14,plain,(
    ! [A_4] :
      ( k1_relat_1(k5_relat_1(A_4,k2_funct_1(A_4))) = k1_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1194,plain,
    ( k1_relat_1(k6_partfun1(k2_struct_0('#skF_1'))) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1186,c_14])).

tff(c_1200,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_58,c_50,c_979,c_1194])).

tff(c_1213,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1200,c_853])).

tff(c_1210,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1200,c_848])).

tff(c_1211,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1200,c_851])).

tff(c_1091,plain,(
    ! [C_158,B_159,A_160] :
      ( m1_subset_1(k2_funct_1(C_158),k1_zfmisc_1(k2_zfmisc_1(B_159,A_160)))
      | k2_relset_1(A_160,B_159,C_158) != B_159
      | ~ v2_funct_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159)))
      | ~ v1_funct_2(C_158,A_160,B_159)
      | ~ v1_funct_1(C_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    ! [A_11,B_12,C_13] :
      ( k2_relset_1(A_11,B_12,C_13) = k2_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1409,plain,(
    ! [B_182,A_183,C_184] :
      ( k2_relset_1(B_182,A_183,k2_funct_1(C_184)) = k2_relat_1(k2_funct_1(C_184))
      | k2_relset_1(A_183,B_182,C_184) != B_182
      | ~ v2_funct_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182)))
      | ~ v1_funct_2(C_184,A_183,B_182)
      | ~ v1_funct_1(C_184) ) ),
    inference(resolution,[status(thm)],[c_1091,c_20])).

tff(c_1412,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1211,c_1409])).

tff(c_1425,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1213,c_50,c_1210,c_1412])).

tff(c_1063,plain,(
    ! [A_155,B_156,C_157] :
      ( k2_tops_2(A_155,B_156,C_157) = k2_funct_1(C_157)
      | ~ v2_funct_1(C_157)
      | k2_relset_1(A_155,B_156,C_157) != B_156
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156)))
      | ~ v1_funct_2(C_157,A_155,B_156)
      | ~ v1_funct_1(C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1066,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_851,c_1063])).

tff(c_1076,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_853,c_848,c_50,c_1066])).

tff(c_10,plain,(
    ! [A_3] :
      ( k1_relat_1(k2_funct_1(A_3)) = k2_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_180,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_relset_1(A_53,B_54,C_55) = k1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_192,plain,(
    ! [A_14] : k1_relset_1(A_14,A_14,k6_partfun1(A_14)) = k1_relat_1(k6_partfun1(A_14)) ),
    inference(resolution,[status(thm)],[c_65,c_180])).

tff(c_359,plain,(
    ! [A_73,B_74,C_75] :
      ( k8_relset_1(A_73,B_74,C_75,B_74) = k1_relset_1(A_73,B_74,C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_363,plain,(
    ! [A_14] : k8_relset_1(A_14,A_14,k6_partfun1(A_14),A_14) = k1_relset_1(A_14,A_14,k6_partfun1(A_14)) ),
    inference(resolution,[status(thm)],[c_65,c_359])).

tff(c_370,plain,(
    ! [A_14] : k1_relat_1(k6_partfun1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_150,c_363])).

tff(c_216,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_227,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_119,c_216])).

tff(c_248,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_120])).

tff(c_257,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_104])).

tff(c_253,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_227])).

tff(c_255,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_119])).

tff(c_534,plain,(
    ! [B_100,C_101,A_102] :
      ( k6_partfun1(B_100) = k5_relat_1(k2_funct_1(C_101),C_101)
      | k1_xboole_0 = B_100
      | ~ v2_funct_1(C_101)
      | k2_relset_1(A_102,B_100,C_101) != B_100
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_100)))
      | ~ v1_funct_2(C_101,A_102,B_100)
      | ~ v1_funct_1(C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_538,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3'))
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_255,c_534])).

tff(c_547,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3'))
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_257,c_253,c_50,c_538])).

tff(c_552,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_547])).

tff(c_256,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_116])).

tff(c_564,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_552,c_256])).

tff(c_568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_564])).

tff(c_570,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_547])).

tff(c_579,plain,(
    ! [A_110,C_111,B_112] :
      ( k6_partfun1(A_110) = k5_relat_1(C_111,k2_funct_1(C_111))
      | k1_xboole_0 = B_112
      | ~ v2_funct_1(C_111)
      | k2_relset_1(A_110,B_112,C_111) != B_112
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_110,B_112)))
      | ~ v1_funct_2(C_111,A_110,B_112)
      | ~ v1_funct_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_583,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_255,c_579])).

tff(c_592,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_257,c_253,c_50,c_583])).

tff(c_593,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_570,c_592])).

tff(c_605,plain,
    ( k1_relat_1(k6_partfun1(k2_struct_0('#skF_1'))) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_14])).

tff(c_611,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_58,c_50,c_370,c_605])).

tff(c_623,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_257])).

tff(c_620,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_253])).

tff(c_621,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_255])).

tff(c_475,plain,(
    ! [C_91,B_92,A_93] :
      ( m1_subset_1(k2_funct_1(C_91),k1_zfmisc_1(k2_zfmisc_1(B_92,A_93)))
      | k2_relset_1(A_93,B_92,C_91) != B_92
      | ~ v2_funct_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92)))
      | ~ v1_funct_2(C_91,A_93,B_92)
      | ~ v1_funct_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_18,plain,(
    ! [A_8,B_9,C_10] :
      ( k1_relset_1(A_8,B_9,C_10) = k1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_506,plain,(
    ! [B_92,A_93,C_91] :
      ( k1_relset_1(B_92,A_93,k2_funct_1(C_91)) = k1_relat_1(k2_funct_1(C_91))
      | k2_relset_1(A_93,B_92,C_91) != B_92
      | ~ v2_funct_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92)))
      | ~ v1_funct_2(C_91,A_93,B_92)
      | ~ v1_funct_1(C_91) ) ),
    inference(resolution,[status(thm)],[c_475,c_18])).

tff(c_688,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_621,c_506])).

tff(c_722,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_623,c_50,c_620,c_688])).

tff(c_452,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_tops_2(A_88,B_89,C_90) = k2_funct_1(C_90)
      | ~ v2_funct_1(C_90)
      | k2_relset_1(A_88,B_89,C_90) != B_89
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_2(C_90,A_88,B_89)
      | ~ v1_funct_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_455,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_255,c_452])).

tff(c_465,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_257,c_253,c_50,c_455])).

tff(c_48,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_178,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_94,c_93,c_93,c_94,c_94,c_93,c_93,c_48])).

tff(c_179,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_317,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_248,c_248,c_179])).

tff(c_470,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_317])).

tff(c_614,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_470])).

tff(c_766,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_722,c_614])).

tff(c_773,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_766])).

tff(c_777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_58,c_50,c_773])).

tff(c_778,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_922,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_843,c_778])).

tff(c_1082,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1076,c_922])).

tff(c_1203,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1200,c_1200,c_1082])).

tff(c_1431,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1425,c_1203])).

tff(c_1438,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1431])).

tff(c_1442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_58,c_50,c_1438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.68  
% 3.93/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.68  %$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.93/1.68  
% 3.93/1.68  %Foreground sorts:
% 3.93/1.68  
% 3.93/1.68  
% 3.93/1.68  %Background operators:
% 3.93/1.68  
% 3.93/1.68  
% 3.93/1.68  %Foreground operators:
% 3.93/1.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.93/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.93/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.93/1.68  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.93/1.68  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.93/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.93/1.68  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.93/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.93/1.68  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.93/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.93/1.68  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.93/1.68  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.93/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.93/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.93/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.93/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.93/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.93/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.93/1.68  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.93/1.68  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.93/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.93/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.93/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.93/1.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.93/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.93/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.93/1.68  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.93/1.68  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.93/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.93/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.93/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.93/1.68  
% 4.28/1.71  tff(f_156, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 4.28/1.71  tff(f_112, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.28/1.71  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.28/1.71  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.28/1.71  tff(f_72, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.28/1.71  tff(f_64, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 4.28/1.71  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.28/1.71  tff(f_28, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.28/1.71  tff(f_30, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.28/1.71  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_relset_1(A, A, k6_partfun1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 4.28/1.71  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 4.28/1.71  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.28/1.71  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.28/1.71  tff(f_108, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 4.28/1.71  tff(f_120, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.28/1.71  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 4.28/1.71  tff(f_92, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.28/1.71  tff(f_132, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 4.28/1.71  tff(c_64, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.28/1.71  tff(c_86, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.28/1.71  tff(c_94, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_86])).
% 4.28/1.71  tff(c_60, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.28/1.71  tff(c_93, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_86])).
% 4.28/1.71  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.28/1.71  tff(c_119, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_93, c_54])).
% 4.28/1.71  tff(c_125, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.28/1.71  tff(c_136, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_119, c_125])).
% 4.28/1.71  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.28/1.71  tff(c_50, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.28/1.71  tff(c_8, plain, (![A_3]: (k2_relat_1(k2_funct_1(A_3))=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.28/1.71  tff(c_28, plain, (![A_18]: (k6_relat_1(A_18)=k6_partfun1(A_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.28/1.71  tff(c_22, plain, (![A_14]: (m1_subset_1(k6_relat_1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.28/1.71  tff(c_65, plain, (![A_14]: (m1_subset_1(k6_partfun1(A_14), k1_zfmisc_1(k2_zfmisc_1(A_14, A_14))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22])).
% 4.28/1.71  tff(c_780, plain, (![A_117, B_118, C_119]: (k1_relset_1(A_117, B_118, C_119)=k1_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.28/1.71  tff(c_792, plain, (![A_14]: (k1_relset_1(A_14, A_14, k6_partfun1(A_14))=k1_relat_1(k6_partfun1(A_14)))), inference(resolution, [status(thm)], [c_65, c_780])).
% 4.28/1.71  tff(c_4, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.28/1.71  tff(c_6, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.28/1.71  tff(c_66, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 4.28/1.71  tff(c_141, plain, (![A_48, B_49]: (k8_relset_1(A_48, A_48, k6_partfun1(A_48), B_49)=B_49 | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.28/1.71  tff(c_150, plain, (![A_2]: (k8_relset_1(A_2, A_2, k6_partfun1(A_2), A_2)=A_2)), inference(resolution, [status(thm)], [c_66, c_141])).
% 4.28/1.71  tff(c_968, plain, (![A_137, B_138, C_139]: (k8_relset_1(A_137, B_138, C_139, B_138)=k1_relset_1(A_137, B_138, C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.28/1.71  tff(c_972, plain, (![A_14]: (k8_relset_1(A_14, A_14, k6_partfun1(A_14), A_14)=k1_relset_1(A_14, A_14, k6_partfun1(A_14)))), inference(resolution, [status(thm)], [c_65, c_968])).
% 4.28/1.71  tff(c_979, plain, (![A_14]: (k1_relat_1(k6_partfun1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_792, c_150, c_972])).
% 4.28/1.71  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.28/1.71  tff(c_820, plain, (![A_123, B_124, C_125]: (k2_relset_1(A_123, B_124, C_125)=k2_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.28/1.71  tff(c_831, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_119, c_820])).
% 4.28/1.71  tff(c_52, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.28/1.71  tff(c_120, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_93, c_52])).
% 4.28/1.71  tff(c_843, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_831, c_120])).
% 4.28/1.71  tff(c_56, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.28/1.71  tff(c_95, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_56])).
% 4.28/1.71  tff(c_104, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95])).
% 4.28/1.71  tff(c_853, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_104])).
% 4.28/1.71  tff(c_848, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_843, c_831])).
% 4.28/1.71  tff(c_851, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_119])).
% 4.28/1.71  tff(c_1150, plain, (![A_168, C_169, B_170]: (k6_partfun1(A_168)=k5_relat_1(C_169, k2_funct_1(C_169)) | k1_xboole_0=B_170 | ~v2_funct_1(C_169) | k2_relset_1(A_168, B_170, C_169)!=B_170 | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_168, B_170))) | ~v1_funct_2(C_169, A_168, B_170) | ~v1_funct_1(C_169))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.28/1.71  tff(c_1154, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_851, c_1150])).
% 4.28/1.71  tff(c_1163, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_853, c_848, c_50, c_1154])).
% 4.28/1.71  tff(c_1168, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1163])).
% 4.28/1.71  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.28/1.71  tff(c_105, plain, (![A_40]: (~v1_xboole_0(u1_struct_0(A_40)) | ~l1_struct_0(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.28/1.71  tff(c_111, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_93, c_105])).
% 4.28/1.71  tff(c_115, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_111])).
% 4.28/1.71  tff(c_116, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_115])).
% 4.28/1.71  tff(c_852, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_116])).
% 4.28/1.71  tff(c_1181, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1168, c_852])).
% 4.28/1.71  tff(c_1185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1181])).
% 4.28/1.71  tff(c_1186, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_1163])).
% 4.28/1.71  tff(c_14, plain, (![A_4]: (k1_relat_1(k5_relat_1(A_4, k2_funct_1(A_4)))=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.28/1.71  tff(c_1194, plain, (k1_relat_1(k6_partfun1(k2_struct_0('#skF_1')))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1186, c_14])).
% 4.28/1.71  tff(c_1200, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_58, c_50, c_979, c_1194])).
% 4.28/1.71  tff(c_1213, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1200, c_853])).
% 4.28/1.71  tff(c_1210, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1200, c_848])).
% 4.28/1.71  tff(c_1211, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1200, c_851])).
% 4.28/1.71  tff(c_1091, plain, (![C_158, B_159, A_160]: (m1_subset_1(k2_funct_1(C_158), k1_zfmisc_1(k2_zfmisc_1(B_159, A_160))) | k2_relset_1(A_160, B_159, C_158)!=B_159 | ~v2_funct_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))) | ~v1_funct_2(C_158, A_160, B_159) | ~v1_funct_1(C_158))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.28/1.71  tff(c_20, plain, (![A_11, B_12, C_13]: (k2_relset_1(A_11, B_12, C_13)=k2_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.28/1.71  tff(c_1409, plain, (![B_182, A_183, C_184]: (k2_relset_1(B_182, A_183, k2_funct_1(C_184))=k2_relat_1(k2_funct_1(C_184)) | k2_relset_1(A_183, B_182, C_184)!=B_182 | ~v2_funct_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))) | ~v1_funct_2(C_184, A_183, B_182) | ~v1_funct_1(C_184))), inference(resolution, [status(thm)], [c_1091, c_20])).
% 4.28/1.71  tff(c_1412, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1211, c_1409])).
% 4.28/1.71  tff(c_1425, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1213, c_50, c_1210, c_1412])).
% 4.28/1.71  tff(c_1063, plain, (![A_155, B_156, C_157]: (k2_tops_2(A_155, B_156, C_157)=k2_funct_1(C_157) | ~v2_funct_1(C_157) | k2_relset_1(A_155, B_156, C_157)!=B_156 | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))) | ~v1_funct_2(C_157, A_155, B_156) | ~v1_funct_1(C_157))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.28/1.71  tff(c_1066, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_851, c_1063])).
% 4.28/1.71  tff(c_1076, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_853, c_848, c_50, c_1066])).
% 4.28/1.71  tff(c_10, plain, (![A_3]: (k1_relat_1(k2_funct_1(A_3))=k2_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.28/1.71  tff(c_180, plain, (![A_53, B_54, C_55]: (k1_relset_1(A_53, B_54, C_55)=k1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.28/1.71  tff(c_192, plain, (![A_14]: (k1_relset_1(A_14, A_14, k6_partfun1(A_14))=k1_relat_1(k6_partfun1(A_14)))), inference(resolution, [status(thm)], [c_65, c_180])).
% 4.28/1.71  tff(c_359, plain, (![A_73, B_74, C_75]: (k8_relset_1(A_73, B_74, C_75, B_74)=k1_relset_1(A_73, B_74, C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.28/1.71  tff(c_363, plain, (![A_14]: (k8_relset_1(A_14, A_14, k6_partfun1(A_14), A_14)=k1_relset_1(A_14, A_14, k6_partfun1(A_14)))), inference(resolution, [status(thm)], [c_65, c_359])).
% 4.28/1.71  tff(c_370, plain, (![A_14]: (k1_relat_1(k6_partfun1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_192, c_150, c_363])).
% 4.28/1.71  tff(c_216, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.28/1.71  tff(c_227, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_119, c_216])).
% 4.28/1.71  tff(c_248, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_120])).
% 4.28/1.71  tff(c_257, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_248, c_104])).
% 4.28/1.71  tff(c_253, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_248, c_227])).
% 4.28/1.71  tff(c_255, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_248, c_119])).
% 4.28/1.71  tff(c_534, plain, (![B_100, C_101, A_102]: (k6_partfun1(B_100)=k5_relat_1(k2_funct_1(C_101), C_101) | k1_xboole_0=B_100 | ~v2_funct_1(C_101) | k2_relset_1(A_102, B_100, C_101)!=B_100 | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_100))) | ~v1_funct_2(C_101, A_102, B_100) | ~v1_funct_1(C_101))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.28/1.71  tff(c_538, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3')) | k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_255, c_534])).
% 4.28/1.71  tff(c_547, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3')) | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_257, c_253, c_50, c_538])).
% 4.28/1.71  tff(c_552, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_547])).
% 4.28/1.71  tff(c_256, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_248, c_116])).
% 4.28/1.71  tff(c_564, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_552, c_256])).
% 4.28/1.71  tff(c_568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_564])).
% 4.28/1.71  tff(c_570, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_547])).
% 4.28/1.71  tff(c_579, plain, (![A_110, C_111, B_112]: (k6_partfun1(A_110)=k5_relat_1(C_111, k2_funct_1(C_111)) | k1_xboole_0=B_112 | ~v2_funct_1(C_111) | k2_relset_1(A_110, B_112, C_111)!=B_112 | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_110, B_112))) | ~v1_funct_2(C_111, A_110, B_112) | ~v1_funct_1(C_111))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.28/1.71  tff(c_583, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_255, c_579])).
% 4.28/1.71  tff(c_592, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_257, c_253, c_50, c_583])).
% 4.28/1.71  tff(c_593, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_570, c_592])).
% 4.28/1.71  tff(c_605, plain, (k1_relat_1(k6_partfun1(k2_struct_0('#skF_1')))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_593, c_14])).
% 4.28/1.71  tff(c_611, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_58, c_50, c_370, c_605])).
% 4.28/1.71  tff(c_623, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_611, c_257])).
% 4.28/1.71  tff(c_620, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_611, c_253])).
% 4.28/1.71  tff(c_621, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_611, c_255])).
% 4.28/1.71  tff(c_475, plain, (![C_91, B_92, A_93]: (m1_subset_1(k2_funct_1(C_91), k1_zfmisc_1(k2_zfmisc_1(B_92, A_93))) | k2_relset_1(A_93, B_92, C_91)!=B_92 | ~v2_funct_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))) | ~v1_funct_2(C_91, A_93, B_92) | ~v1_funct_1(C_91))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.28/1.71  tff(c_18, plain, (![A_8, B_9, C_10]: (k1_relset_1(A_8, B_9, C_10)=k1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.28/1.71  tff(c_506, plain, (![B_92, A_93, C_91]: (k1_relset_1(B_92, A_93, k2_funct_1(C_91))=k1_relat_1(k2_funct_1(C_91)) | k2_relset_1(A_93, B_92, C_91)!=B_92 | ~v2_funct_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))) | ~v1_funct_2(C_91, A_93, B_92) | ~v1_funct_1(C_91))), inference(resolution, [status(thm)], [c_475, c_18])).
% 4.28/1.71  tff(c_688, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_621, c_506])).
% 4.28/1.71  tff(c_722, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_623, c_50, c_620, c_688])).
% 4.28/1.71  tff(c_452, plain, (![A_88, B_89, C_90]: (k2_tops_2(A_88, B_89, C_90)=k2_funct_1(C_90) | ~v2_funct_1(C_90) | k2_relset_1(A_88, B_89, C_90)!=B_89 | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_2(C_90, A_88, B_89) | ~v1_funct_1(C_90))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.28/1.71  tff(c_455, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_255, c_452])).
% 4.28/1.71  tff(c_465, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_257, c_253, c_50, c_455])).
% 4.28/1.71  tff(c_48, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.28/1.71  tff(c_178, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_94, c_93, c_93, c_94, c_94, c_93, c_93, c_48])).
% 4.28/1.71  tff(c_179, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_178])).
% 4.28/1.71  tff(c_317, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_248, c_248, c_248, c_179])).
% 4.28/1.71  tff(c_470, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_465, c_317])).
% 4.28/1.71  tff(c_614, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_611, c_470])).
% 4.28/1.71  tff(c_766, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_722, c_614])).
% 4.28/1.71  tff(c_773, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_766])).
% 4.28/1.71  tff(c_777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_58, c_50, c_773])).
% 4.28/1.71  tff(c_778, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_178])).
% 4.28/1.71  tff(c_922, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_843, c_843, c_778])).
% 4.28/1.71  tff(c_1082, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1076, c_922])).
% 4.28/1.71  tff(c_1203, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1200, c_1200, c_1082])).
% 4.28/1.71  tff(c_1431, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1425, c_1203])).
% 4.28/1.71  tff(c_1438, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_1431])).
% 4.28/1.71  tff(c_1442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_58, c_50, c_1438])).
% 4.28/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.71  
% 4.28/1.71  Inference rules
% 4.28/1.71  ----------------------
% 4.28/1.71  #Ref     : 0
% 4.28/1.71  #Sup     : 321
% 4.28/1.71  #Fact    : 0
% 4.28/1.71  #Define  : 0
% 4.28/1.71  #Split   : 4
% 4.28/1.71  #Chain   : 0
% 4.28/1.71  #Close   : 0
% 4.28/1.71  
% 4.28/1.71  Ordering : KBO
% 4.28/1.71  
% 4.28/1.71  Simplification rules
% 4.28/1.71  ----------------------
% 4.28/1.71  #Subsume      : 4
% 4.28/1.71  #Demod        : 357
% 4.28/1.71  #Tautology    : 202
% 4.28/1.71  #SimpNegUnit  : 8
% 4.28/1.71  #BackRed      : 77
% 4.28/1.71  
% 4.28/1.71  #Partial instantiations: 0
% 4.28/1.71  #Strategies tried      : 1
% 4.28/1.71  
% 4.28/1.71  Timing (in seconds)
% 4.28/1.71  ----------------------
% 4.28/1.71  Preprocessing        : 0.36
% 4.28/1.71  Parsing              : 0.19
% 4.28/1.71  CNF conversion       : 0.02
% 4.28/1.71  Main loop            : 0.56
% 4.28/1.71  Inferencing          : 0.20
% 4.28/1.71  Reduction            : 0.20
% 4.28/1.72  Demodulation         : 0.14
% 4.28/1.72  BG Simplification    : 0.03
% 4.28/1.72  Subsumption          : 0.08
% 4.28/1.72  Abstraction          : 0.03
% 4.28/1.72  MUC search           : 0.00
% 4.28/1.72  Cooper               : 0.00
% 4.28/1.72  Total                : 0.98
% 4.28/1.72  Index Insertion      : 0.00
% 4.28/1.72  Index Deletion       : 0.00
% 4.28/1.72  Index Matching       : 0.00
% 4.28/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
