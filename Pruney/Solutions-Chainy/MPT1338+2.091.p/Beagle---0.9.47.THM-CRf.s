%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:27 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  125 (4040 expanded)
%              Number of leaves         :   37 (1449 expanded)
%              Depth                    :   18
%              Number of atoms          :  207 (12582 expanded)
%              Number of equality atoms :   78 (4761 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_131,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
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

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_58,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_66,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_58])).

tff(c_52,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_65,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_58])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_91,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_65,c_46])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_94,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_91,c_4])).

tff(c_97,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_94])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_42,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_8,plain,(
    ! [A_6] :
      ( k2_relat_1(k2_funct_1(A_6)) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_122,plain,(
    ! [A_37,B_38,C_39] :
      ( k2_relset_1(A_37,B_38,C_39) = k2_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_126,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_91,c_122])).

tff(c_44,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_98,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_65,c_44])).

tff(c_127,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_98])).

tff(c_48,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_71,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_48])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_71])).

tff(c_140,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_72])).

tff(c_132,plain,(
    ! [A_40,B_41,C_42] :
      ( k1_relset_1(A_40,B_41,C_42) = k1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_136,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_91,c_132])).

tff(c_395,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_136])).

tff(c_138,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_91])).

tff(c_427,plain,(
    ! [B_79,A_80,C_81] :
      ( k1_xboole_0 = B_79
      | k1_relset_1(A_80,B_79,C_81) = A_80
      | ~ v1_funct_2(C_81,A_80,B_79)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_430,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_138,c_427])).

tff(c_433,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_395,c_430])).

tff(c_434,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_433])).

tff(c_440,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_140])).

tff(c_438,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_138])).

tff(c_137,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_126])).

tff(c_437,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_137])).

tff(c_555,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_tops_2(A_94,B_95,C_96) = k2_funct_1(C_96)
      | ~ v2_funct_1(C_96)
      | k2_relset_1(A_94,B_95,C_96) != B_95
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_2(C_96,A_94,B_95)
      | ~ v1_funct_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_561,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_438,c_555])).

tff(c_565,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_440,c_437,c_42,c_561])).

tff(c_34,plain,(
    ! [A_21,B_22,C_23] :
      ( m1_subset_1(k2_tops_2(A_21,B_22,C_23),k1_zfmisc_1(k2_zfmisc_1(B_22,A_21)))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_2(C_23,A_21,B_22)
      | ~ v1_funct_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_573,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_34])).

tff(c_577,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_440,c_438,c_573])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( k2_relset_1(A_10,B_11,C_12) = k2_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_640,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_577,c_14])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_relat_1(k2_funct_1(A_6)) = k2_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_158,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_136])).

tff(c_199,plain,(
    ! [B_55,A_56,C_57] :
      ( k1_xboole_0 = B_55
      | k1_relset_1(A_56,B_55,C_57) = A_56
      | ~ v1_funct_2(C_57,A_56,B_55)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_56,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_202,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_138,c_199])).

tff(c_205,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_158,c_202])).

tff(c_206,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_212,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_140])).

tff(c_209,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_137])).

tff(c_210,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_138])).

tff(c_347,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_tops_2(A_70,B_71,C_72) = k2_funct_1(C_72)
      | ~ v2_funct_1(C_72)
      | k2_relset_1(A_70,B_71,C_72) != B_71
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ v1_funct_2(C_72,A_70,B_71)
      | ~ v1_funct_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_353,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_210,c_347])).

tff(c_357,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_212,c_209,c_42,c_353])).

tff(c_275,plain,(
    ! [A_61,B_62,C_63] :
      ( m1_subset_1(k2_tops_2(A_61,B_62,C_63),k1_zfmisc_1(k2_zfmisc_1(B_62,A_61)))
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_2(C_63,A_61,B_62)
      | ~ v1_funct_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] :
      ( k1_relset_1(A_7,B_8,C_9) = k1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_333,plain,(
    ! [B_67,A_68,C_69] :
      ( k1_relset_1(B_67,A_68,k2_tops_2(A_68,B_67,C_69)) = k1_relat_1(k2_tops_2(A_68,B_67,C_69))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_68,B_67)))
      | ~ v1_funct_2(C_69,A_68,B_67)
      | ~ v1_funct_1(C_69) ) ),
    inference(resolution,[status(thm)],[c_275,c_12])).

tff(c_337,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) = k1_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_210,c_333])).

tff(c_341,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) = k1_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_212,c_337])).

tff(c_141,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_65])).

tff(c_40,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_156,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_141,c_127,c_66,c_66,c_141,c_141,c_66,c_66,c_40])).

tff(c_157,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_208,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_206,c_157])).

tff(c_342,plain,(
    k1_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_208])).

tff(c_358,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_342])).

tff(c_374,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_358])).

tff(c_378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_50,c_42,c_374])).

tff(c_379,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_77,plain,(
    ! [A_31] :
      ( ~ v1_xboole_0(u1_struct_0(A_31))
      | ~ l1_struct_0(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_83,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_77])).

tff(c_87,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_83])).

tff(c_88,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_87])).

tff(c_139,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_88])).

tff(c_388,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_139])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_388])).

tff(c_393,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_435,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_434,c_434,c_393])).

tff(c_568,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_435])).

tff(c_660,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_568])).

tff(c_667,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_660])).

tff(c_671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_50,c_42,c_667])).

tff(c_672,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_681,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_139])).

tff(c_685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_681])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.32  % Computer   : n007.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 16:20:36 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.47  
% 3.18/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.47  %$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.18/1.47  
% 3.18/1.47  %Foreground sorts:
% 3.18/1.47  
% 3.18/1.47  
% 3.18/1.47  %Background operators:
% 3.18/1.47  
% 3.18/1.47  
% 3.18/1.47  %Foreground operators:
% 3.18/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.18/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.18/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.18/1.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.18/1.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.18/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.18/1.47  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.18/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.18/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.18/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.18/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.18/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.18/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.18/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.18/1.47  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.18/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.18/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.18/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.18/1.47  
% 3.22/1.49  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.22/1.49  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.22/1.49  tff(f_131, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 3.22/1.49  tff(f_75, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.22/1.49  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.22/1.49  tff(f_45, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.22/1.49  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.22/1.49  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.22/1.49  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.22/1.49  tff(f_95, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.22/1.49  tff(f_107, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 3.22/1.49  tff(f_83, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.22/1.49  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.22/1.49  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.49  tff(c_56, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.22/1.49  tff(c_58, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.22/1.49  tff(c_66, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_58])).
% 3.22/1.49  tff(c_52, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.22/1.49  tff(c_65, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_58])).
% 3.22/1.49  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.22/1.49  tff(c_91, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_65, c_46])).
% 3.22/1.49  tff(c_4, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.22/1.49  tff(c_94, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_91, c_4])).
% 3.22/1.49  tff(c_97, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_94])).
% 3.22/1.49  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.22/1.49  tff(c_42, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.22/1.49  tff(c_8, plain, (![A_6]: (k2_relat_1(k2_funct_1(A_6))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.22/1.49  tff(c_122, plain, (![A_37, B_38, C_39]: (k2_relset_1(A_37, B_38, C_39)=k2_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.22/1.49  tff(c_126, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_91, c_122])).
% 3.22/1.49  tff(c_44, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.22/1.49  tff(c_98, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_65, c_44])).
% 3.22/1.49  tff(c_127, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_98])).
% 3.22/1.49  tff(c_48, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.22/1.49  tff(c_71, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_48])).
% 3.22/1.49  tff(c_72, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_71])).
% 3.22/1.49  tff(c_140, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_72])).
% 3.22/1.49  tff(c_132, plain, (![A_40, B_41, C_42]: (k1_relset_1(A_40, B_41, C_42)=k1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.22/1.49  tff(c_136, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_91, c_132])).
% 3.22/1.49  tff(c_395, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_136])).
% 3.22/1.49  tff(c_138, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_91])).
% 3.22/1.49  tff(c_427, plain, (![B_79, A_80, C_81]: (k1_xboole_0=B_79 | k1_relset_1(A_80, B_79, C_81)=A_80 | ~v1_funct_2(C_81, A_80, B_79) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.22/1.49  tff(c_430, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_138, c_427])).
% 3.22/1.49  tff(c_433, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_395, c_430])).
% 3.22/1.49  tff(c_434, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_433])).
% 3.22/1.49  tff(c_440, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_434, c_140])).
% 3.22/1.49  tff(c_438, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_434, c_138])).
% 3.22/1.49  tff(c_137, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_126])).
% 3.22/1.49  tff(c_437, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_434, c_137])).
% 3.22/1.49  tff(c_555, plain, (![A_94, B_95, C_96]: (k2_tops_2(A_94, B_95, C_96)=k2_funct_1(C_96) | ~v2_funct_1(C_96) | k2_relset_1(A_94, B_95, C_96)!=B_95 | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_2(C_96, A_94, B_95) | ~v1_funct_1(C_96))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.22/1.49  tff(c_561, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_438, c_555])).
% 3.22/1.49  tff(c_565, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_440, c_437, c_42, c_561])).
% 3.22/1.49  tff(c_34, plain, (![A_21, B_22, C_23]: (m1_subset_1(k2_tops_2(A_21, B_22, C_23), k1_zfmisc_1(k2_zfmisc_1(B_22, A_21))) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_2(C_23, A_21, B_22) | ~v1_funct_1(C_23))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.22/1.49  tff(c_573, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_565, c_34])).
% 3.22/1.49  tff(c_577, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_440, c_438, c_573])).
% 3.22/1.49  tff(c_14, plain, (![A_10, B_11, C_12]: (k2_relset_1(A_10, B_11, C_12)=k2_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.22/1.49  tff(c_640, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_577, c_14])).
% 3.22/1.49  tff(c_10, plain, (![A_6]: (k1_relat_1(k2_funct_1(A_6))=k2_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.22/1.49  tff(c_158, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_136])).
% 3.22/1.49  tff(c_199, plain, (![B_55, A_56, C_57]: (k1_xboole_0=B_55 | k1_relset_1(A_56, B_55, C_57)=A_56 | ~v1_funct_2(C_57, A_56, B_55) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_56, B_55))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.22/1.49  tff(c_202, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_138, c_199])).
% 3.22/1.49  tff(c_205, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_158, c_202])).
% 3.22/1.49  tff(c_206, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_205])).
% 3.22/1.49  tff(c_212, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_140])).
% 3.22/1.49  tff(c_209, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_137])).
% 3.22/1.49  tff(c_210, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_138])).
% 3.22/1.49  tff(c_347, plain, (![A_70, B_71, C_72]: (k2_tops_2(A_70, B_71, C_72)=k2_funct_1(C_72) | ~v2_funct_1(C_72) | k2_relset_1(A_70, B_71, C_72)!=B_71 | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~v1_funct_2(C_72, A_70, B_71) | ~v1_funct_1(C_72))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.22/1.49  tff(c_353, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_210, c_347])).
% 3.22/1.49  tff(c_357, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_212, c_209, c_42, c_353])).
% 3.22/1.49  tff(c_275, plain, (![A_61, B_62, C_63]: (m1_subset_1(k2_tops_2(A_61, B_62, C_63), k1_zfmisc_1(k2_zfmisc_1(B_62, A_61))) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_2(C_63, A_61, B_62) | ~v1_funct_1(C_63))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.22/1.49  tff(c_12, plain, (![A_7, B_8, C_9]: (k1_relset_1(A_7, B_8, C_9)=k1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.22/1.49  tff(c_333, plain, (![B_67, A_68, C_69]: (k1_relset_1(B_67, A_68, k2_tops_2(A_68, B_67, C_69))=k1_relat_1(k2_tops_2(A_68, B_67, C_69)) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_68, B_67))) | ~v1_funct_2(C_69, A_68, B_67) | ~v1_funct_1(C_69))), inference(resolution, [status(thm)], [c_275, c_12])).
% 3.22/1.49  tff(c_337, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))=k1_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_210, c_333])).
% 3.22/1.49  tff(c_341, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))=k1_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_212, c_337])).
% 3.22/1.49  tff(c_141, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_65])).
% 3.22/1.49  tff(c_40, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.22/1.49  tff(c_156, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_141, c_127, c_66, c_66, c_141, c_141, c_66, c_66, c_40])).
% 3.22/1.49  tff(c_157, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_156])).
% 3.22/1.49  tff(c_208, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_206, c_206, c_157])).
% 3.22/1.49  tff(c_342, plain, (k1_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_341, c_208])).
% 3.22/1.49  tff(c_358, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_342])).
% 3.22/1.49  tff(c_374, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_358])).
% 3.22/1.49  tff(c_378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_50, c_42, c_374])).
% 3.22/1.49  tff(c_379, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_205])).
% 3.22/1.49  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.22/1.49  tff(c_77, plain, (![A_31]: (~v1_xboole_0(u1_struct_0(A_31)) | ~l1_struct_0(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.22/1.49  tff(c_83, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_65, c_77])).
% 3.22/1.49  tff(c_87, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_83])).
% 3.22/1.49  tff(c_88, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_87])).
% 3.22/1.49  tff(c_139, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_88])).
% 3.22/1.49  tff(c_388, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_379, c_139])).
% 3.22/1.49  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_388])).
% 3.22/1.49  tff(c_393, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_156])).
% 3.22/1.49  tff(c_435, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_434, c_434, c_434, c_393])).
% 3.22/1.49  tff(c_568, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_565, c_435])).
% 3.22/1.49  tff(c_660, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_640, c_568])).
% 3.22/1.49  tff(c_667, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_660])).
% 3.22/1.49  tff(c_671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_50, c_42, c_667])).
% 3.22/1.49  tff(c_672, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_433])).
% 3.22/1.49  tff(c_681, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_672, c_139])).
% 3.22/1.49  tff(c_685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_681])).
% 3.22/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.49  
% 3.22/1.49  Inference rules
% 3.22/1.49  ----------------------
% 3.22/1.49  #Ref     : 0
% 3.22/1.49  #Sup     : 135
% 3.22/1.49  #Fact    : 0
% 3.22/1.49  #Define  : 0
% 3.22/1.49  #Split   : 4
% 3.22/1.49  #Chain   : 0
% 3.22/1.49  #Close   : 0
% 3.22/1.49  
% 3.22/1.49  Ordering : KBO
% 3.22/1.49  
% 3.22/1.49  Simplification rules
% 3.22/1.49  ----------------------
% 3.22/1.49  #Subsume      : 8
% 3.22/1.49  #Demod        : 178
% 3.22/1.49  #Tautology    : 79
% 3.22/1.49  #SimpNegUnit  : 2
% 3.22/1.49  #BackRed      : 52
% 3.22/1.49  
% 3.22/1.49  #Partial instantiations: 0
% 3.22/1.49  #Strategies tried      : 1
% 3.22/1.49  
% 3.22/1.49  Timing (in seconds)
% 3.22/1.49  ----------------------
% 3.22/1.49  Preprocessing        : 0.36
% 3.22/1.49  Parsing              : 0.19
% 3.22/1.49  CNF conversion       : 0.02
% 3.22/1.49  Main loop            : 0.37
% 3.22/1.49  Inferencing          : 0.13
% 3.22/1.49  Reduction            : 0.13
% 3.22/1.49  Demodulation         : 0.09
% 3.22/1.49  BG Simplification    : 0.02
% 3.22/1.49  Subsumption          : 0.06
% 3.22/1.49  Abstraction          : 0.02
% 3.22/1.49  MUC search           : 0.00
% 3.22/1.49  Cooper               : 0.00
% 3.22/1.49  Total                : 0.77
% 3.22/1.49  Index Insertion      : 0.00
% 3.22/1.49  Index Deletion       : 0.00
% 3.22/1.49  Index Matching       : 0.00
% 3.22/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
