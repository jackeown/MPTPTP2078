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
% DateTime   : Thu Dec  3 10:23:21 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  156 (63716 expanded)
%              Number of leaves         :   36 (22734 expanded)
%              Depth                    :   25
%              Number of atoms          :  265 (201049 expanded)
%              Number of equality atoms :  107 (76450 expanded)
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

tff(f_126,negated_conjecture,(
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

tff(f_70,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_54,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_55,plain,(
    ! [A_26] :
      ( u1_struct_0(A_26) = k2_struct_0(A_26)
      | ~ l1_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_63,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_55])).

tff(c_50,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_62,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_55])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_62,c_44])).

tff(c_8,plain,(
    ! [C_4,A_2,B_3] :
      ( v1_relat_1(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(A_2,B_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_84,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_8])).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_40,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4,plain,(
    ! [A_1] :
      ( k2_relat_1(k2_funct_1(A_1)) = k1_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1051,plain,(
    ! [A_92,B_93,C_94] :
      ( k2_relset_1(A_92,B_93,C_94) = k2_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1055,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1051])).

tff(c_42,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_74,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_62,c_42])).

tff(c_1057,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_74])).

tff(c_46,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_62,c_46])).

tff(c_1065,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_72])).

tff(c_103,plain,(
    ! [A_33,B_34,C_35] :
      ( k1_relset_1(A_33,B_34,C_35) = k1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_107,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_103])).

tff(c_1063,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_107])).

tff(c_1064,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_80])).

tff(c_1125,plain,(
    ! [B_107,A_108,C_109] :
      ( k1_xboole_0 = B_107
      | k1_relset_1(A_108,B_107,C_109) = A_108
      | ~ v1_funct_2(C_109,A_108,B_107)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1128,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1064,c_1125])).

tff(c_1131,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1065,c_1063,c_1128])).

tff(c_1132,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1131])).

tff(c_1139,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1132,c_1065])).

tff(c_1062,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_1055])).

tff(c_1138,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1132,c_1062])).

tff(c_1136,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1132,c_1064])).

tff(c_1275,plain,(
    ! [A_122,B_123,C_124] :
      ( k2_tops_2(A_122,B_123,C_124) = k2_funct_1(C_124)
      | ~ v2_funct_1(C_124)
      | k2_relset_1(A_122,B_123,C_124) != B_123
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | ~ v1_funct_2(C_124,A_122,B_123)
      | ~ v1_funct_1(C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1281,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1136,c_1275])).

tff(c_1285,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1139,c_1138,c_40,c_1281])).

tff(c_1201,plain,(
    ! [A_113,B_114,C_115] :
      ( m1_subset_1(k2_tops_2(A_113,B_114,C_115),k1_zfmisc_1(k2_zfmisc_1(B_114,A_113)))
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ v1_funct_2(C_115,A_113,B_114)
      | ~ v1_funct_1(C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( k2_relset_1(A_8,B_9,C_10) = k2_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1261,plain,(
    ! [B_119,A_120,C_121] :
      ( k2_relset_1(B_119,A_120,k2_tops_2(A_120,B_119,C_121)) = k2_relat_1(k2_tops_2(A_120,B_119,C_121))
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119)))
      | ~ v1_funct_2(C_121,A_120,B_119)
      | ~ v1_funct_1(C_121) ) ),
    inference(resolution,[status(thm)],[c_1201,c_12])).

tff(c_1265,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) = k2_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1136,c_1261])).

tff(c_1269,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) = k2_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1139,c_1265])).

tff(c_115,plain,(
    ! [A_37,B_38,C_39] :
      ( k2_relset_1(A_37,B_38,C_39) = k2_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_119,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_115])).

tff(c_120,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_74])).

tff(c_128,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_72])).

tff(c_126,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_107])).

tff(c_127,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_80])).

tff(c_178,plain,(
    ! [B_49,A_50,C_51] :
      ( k1_xboole_0 = B_49
      | k1_relset_1(A_50,B_49,C_51) = A_50
      | ~ v1_funct_2(C_51,A_50,B_49)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_181,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_127,c_178])).

tff(c_184,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_126,c_181])).

tff(c_185,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_191,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_128])).

tff(c_125,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_119])).

tff(c_190,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_125])).

tff(c_189,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_127])).

tff(c_480,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_tops_2(A_76,B_77,C_78) = k2_funct_1(C_78)
      | ~ v2_funct_1(C_78)
      | k2_relset_1(A_76,B_77,C_78) != B_77
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ v1_funct_2(C_78,A_76,B_77)
      | ~ v1_funct_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_486,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_189,c_480])).

tff(c_490,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_191,c_190,c_40,c_486])).

tff(c_38,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_112,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_63,c_62,c_62,c_63,c_63,c_62,c_62,c_38])).

tff(c_113,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_168,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_120,c_120,c_113])).

tff(c_187,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_185,c_168])).

tff(c_493,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_187])).

tff(c_420,plain,(
    ! [A_67,B_68,C_69] :
      ( v1_funct_2(k2_tops_2(A_67,B_68,C_69),B_68,A_67)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_2(C_69,A_67,B_68)
      | ~ v1_funct_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_422,plain,
    ( v1_funct_2(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_189,c_420])).

tff(c_425,plain,(
    v1_funct_2(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_191,c_422])).

tff(c_492,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_425])).

tff(c_32,plain,(
    ! [A_19,B_20,C_21] :
      ( m1_subset_1(k2_tops_2(A_19,B_20,C_21),k1_zfmisc_1(k2_zfmisc_1(B_20,A_19)))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(C_21,A_19,B_20)
      | ~ v1_funct_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_498,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_490,c_32])).

tff(c_502,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_191,c_189,c_498])).

tff(c_24,plain,(
    ! [B_12,A_11,C_13] :
      ( k1_xboole_0 = B_12
      | k1_relset_1(A_11,B_12,C_13) = A_11
      | ~ v1_funct_2(C_13,A_11,B_12)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_528,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_502,c_24])).

tff(c_557,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_528])).

tff(c_558,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_557])).

tff(c_568,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_492])).

tff(c_566,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_502])).

tff(c_16,plain,(
    ! [C_13,A_11] :
      ( k1_xboole_0 = C_13
      | ~ v1_funct_2(C_13,A_11,k1_xboole_0)
      | k1_xboole_0 = A_11
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_723,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_xboole_0)
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_566,c_16])).

tff(c_760,plain,
    ( k2_funct_1('#skF_3') = k1_xboole_0
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_568,c_723])).

tff(c_766,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_760])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_28,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(k2_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_133,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_28])).

tff(c_137,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_133])).

tff(c_138,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_137])).

tff(c_783,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_138])).

tff(c_787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_783])).

tff(c_788,plain,(
    k2_funct_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_760])).

tff(c_6,plain,(
    ! [A_1] :
      ( k1_relat_1(k2_funct_1(A_1)) = k2_relat_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_801,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1(k1_xboole_0)
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_788,c_6])).

tff(c_808,plain,(
    k2_relat_1('#skF_3') = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_48,c_40,c_801])).

tff(c_426,plain,(
    ! [A_70,B_71,C_72] :
      ( m1_subset_1(k2_tops_2(A_70,B_71,C_72),k1_zfmisc_1(k2_zfmisc_1(B_71,A_70)))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ v1_funct_2(C_72,A_70,B_71)
      | ~ v1_funct_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( k1_relset_1(A_5,B_6,C_7) = k1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_504,plain,(
    ! [B_79,A_80,C_81] :
      ( k1_relset_1(B_79,A_80,k2_tops_2(A_80,B_79,C_81)) = k1_relat_1(k2_tops_2(A_80,B_79,C_81))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79)))
      | ~ v1_funct_2(C_81,A_80,B_79)
      | ~ v1_funct_1(C_81) ) ),
    inference(resolution,[status(thm)],[c_426,c_10])).

tff(c_508,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) = k1_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_189,c_504])).

tff(c_512,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_191,c_490,c_490,c_508])).

tff(c_692,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_xboole_0,k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_512])).

tff(c_793,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_788,c_692])).

tff(c_868,plain,(
    k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_793])).

tff(c_567,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_xboole_0,k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_493])).

tff(c_812,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_xboole_0,k1_xboole_0) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_567])).

tff(c_817,plain,(
    k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_808,c_812])).

tff(c_1033,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_868,c_817])).

tff(c_1034,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_1043,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_138])).

tff(c_1047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1043])).

tff(c_1048,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_1110,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_1057,c_1048])).

tff(c_1134,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1132,c_1132,c_1132,c_1110])).

tff(c_1270,plain,(
    k2_relat_1(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1269,c_1134])).

tff(c_1304,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1285,c_1270])).

tff(c_1307,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1304])).

tff(c_1311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_48,c_40,c_1307])).

tff(c_1312,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1131])).

tff(c_1070,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1057,c_28])).

tff(c_1074,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1070])).

tff(c_1075,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1074])).

tff(c_1322,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1312,c_1075])).

tff(c_1326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1322])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:57:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.53  
% 3.49/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.54  %$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.57/1.54  
% 3.57/1.54  %Foreground sorts:
% 3.57/1.54  
% 3.57/1.54  
% 3.57/1.54  %Background operators:
% 3.57/1.54  
% 3.57/1.54  
% 3.57/1.54  %Foreground operators:
% 3.57/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.57/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.57/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.57/1.54  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.57/1.54  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.57/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.57/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.57/1.54  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.57/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.57/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.57/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.57/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.57/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.57/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.57/1.54  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.57/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.57/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.57/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.57/1.54  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.57/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.57/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.57/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.57/1.54  
% 3.57/1.56  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.57/1.56  tff(f_126, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 3.57/1.56  tff(f_70, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.57/1.56  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.57/1.56  tff(f_36, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.57/1.56  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.57/1.56  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.57/1.56  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.57/1.56  tff(f_90, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.57/1.56  tff(f_102, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 3.57/1.56  tff(f_78, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.57/1.56  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.57/1.56  tff(c_54, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.57/1.56  tff(c_55, plain, (![A_26]: (u1_struct_0(A_26)=k2_struct_0(A_26) | ~l1_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.57/1.56  tff(c_63, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_55])).
% 3.57/1.56  tff(c_50, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.57/1.56  tff(c_62, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_55])).
% 3.57/1.56  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.57/1.56  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_62, c_44])).
% 3.57/1.56  tff(c_8, plain, (![C_4, A_2, B_3]: (v1_relat_1(C_4) | ~m1_subset_1(C_4, k1_zfmisc_1(k2_zfmisc_1(A_2, B_3))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.57/1.56  tff(c_84, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_8])).
% 3.57/1.56  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.57/1.56  tff(c_40, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.57/1.56  tff(c_4, plain, (![A_1]: (k2_relat_1(k2_funct_1(A_1))=k1_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.57/1.56  tff(c_1051, plain, (![A_92, B_93, C_94]: (k2_relset_1(A_92, B_93, C_94)=k2_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.57/1.56  tff(c_1055, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_1051])).
% 3.57/1.56  tff(c_42, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.57/1.56  tff(c_74, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_62, c_42])).
% 3.57/1.56  tff(c_1057, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_74])).
% 3.57/1.56  tff(c_46, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.57/1.56  tff(c_72, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_62, c_46])).
% 3.57/1.56  tff(c_1065, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_72])).
% 3.57/1.56  tff(c_103, plain, (![A_33, B_34, C_35]: (k1_relset_1(A_33, B_34, C_35)=k1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.57/1.56  tff(c_107, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_103])).
% 3.57/1.56  tff(c_1063, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_107])).
% 3.57/1.56  tff(c_1064, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_80])).
% 3.57/1.56  tff(c_1125, plain, (![B_107, A_108, C_109]: (k1_xboole_0=B_107 | k1_relset_1(A_108, B_107, C_109)=A_108 | ~v1_funct_2(C_109, A_108, B_107) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.57/1.56  tff(c_1128, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1064, c_1125])).
% 3.57/1.56  tff(c_1131, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1065, c_1063, c_1128])).
% 3.57/1.56  tff(c_1132, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1131])).
% 3.57/1.56  tff(c_1139, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1132, c_1065])).
% 3.57/1.56  tff(c_1062, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_1055])).
% 3.57/1.56  tff(c_1138, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1132, c_1062])).
% 3.57/1.56  tff(c_1136, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1132, c_1064])).
% 3.57/1.56  tff(c_1275, plain, (![A_122, B_123, C_124]: (k2_tops_2(A_122, B_123, C_124)=k2_funct_1(C_124) | ~v2_funct_1(C_124) | k2_relset_1(A_122, B_123, C_124)!=B_123 | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | ~v1_funct_2(C_124, A_122, B_123) | ~v1_funct_1(C_124))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.57/1.56  tff(c_1281, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1136, c_1275])).
% 3.57/1.56  tff(c_1285, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1139, c_1138, c_40, c_1281])).
% 3.57/1.56  tff(c_1201, plain, (![A_113, B_114, C_115]: (m1_subset_1(k2_tops_2(A_113, B_114, C_115), k1_zfmisc_1(k2_zfmisc_1(B_114, A_113))) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~v1_funct_2(C_115, A_113, B_114) | ~v1_funct_1(C_115))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.57/1.56  tff(c_12, plain, (![A_8, B_9, C_10]: (k2_relset_1(A_8, B_9, C_10)=k2_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.57/1.56  tff(c_1261, plain, (![B_119, A_120, C_121]: (k2_relset_1(B_119, A_120, k2_tops_2(A_120, B_119, C_121))=k2_relat_1(k2_tops_2(A_120, B_119, C_121)) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))) | ~v1_funct_2(C_121, A_120, B_119) | ~v1_funct_1(C_121))), inference(resolution, [status(thm)], [c_1201, c_12])).
% 3.57/1.56  tff(c_1265, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))=k2_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1136, c_1261])).
% 3.57/1.56  tff(c_1269, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))=k2_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1139, c_1265])).
% 3.57/1.56  tff(c_115, plain, (![A_37, B_38, C_39]: (k2_relset_1(A_37, B_38, C_39)=k2_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.57/1.56  tff(c_119, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_115])).
% 3.57/1.56  tff(c_120, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_74])).
% 3.57/1.56  tff(c_128, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_72])).
% 3.57/1.56  tff(c_126, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_107])).
% 3.57/1.56  tff(c_127, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_80])).
% 3.57/1.56  tff(c_178, plain, (![B_49, A_50, C_51]: (k1_xboole_0=B_49 | k1_relset_1(A_50, B_49, C_51)=A_50 | ~v1_funct_2(C_51, A_50, B_49) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.57/1.56  tff(c_181, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_127, c_178])).
% 3.57/1.56  tff(c_184, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_126, c_181])).
% 3.57/1.56  tff(c_185, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_184])).
% 3.57/1.56  tff(c_191, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_128])).
% 3.57/1.56  tff(c_125, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_119])).
% 3.57/1.56  tff(c_190, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_125])).
% 3.57/1.56  tff(c_189, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_127])).
% 3.57/1.56  tff(c_480, plain, (![A_76, B_77, C_78]: (k2_tops_2(A_76, B_77, C_78)=k2_funct_1(C_78) | ~v2_funct_1(C_78) | k2_relset_1(A_76, B_77, C_78)!=B_77 | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~v1_funct_2(C_78, A_76, B_77) | ~v1_funct_1(C_78))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.57/1.56  tff(c_486, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_189, c_480])).
% 3.57/1.56  tff(c_490, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_191, c_190, c_40, c_486])).
% 3.57/1.56  tff(c_38, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.57/1.56  tff(c_112, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_63, c_62, c_62, c_63, c_63, c_62, c_62, c_38])).
% 3.57/1.56  tff(c_113, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_112])).
% 3.57/1.56  tff(c_168, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_120, c_120, c_113])).
% 3.57/1.56  tff(c_187, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_185, c_168])).
% 3.57/1.56  tff(c_493, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_490, c_187])).
% 3.57/1.56  tff(c_420, plain, (![A_67, B_68, C_69]: (v1_funct_2(k2_tops_2(A_67, B_68, C_69), B_68, A_67) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~v1_funct_2(C_69, A_67, B_68) | ~v1_funct_1(C_69))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.57/1.56  tff(c_422, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_189, c_420])).
% 3.57/1.56  tff(c_425, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_191, c_422])).
% 3.57/1.56  tff(c_492, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_425])).
% 3.57/1.56  tff(c_32, plain, (![A_19, B_20, C_21]: (m1_subset_1(k2_tops_2(A_19, B_20, C_21), k1_zfmisc_1(k2_zfmisc_1(B_20, A_19))) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(C_21, A_19, B_20) | ~v1_funct_1(C_21))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.57/1.56  tff(c_498, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_490, c_32])).
% 3.57/1.56  tff(c_502, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_191, c_189, c_498])).
% 3.57/1.56  tff(c_24, plain, (![B_12, A_11, C_13]: (k1_xboole_0=B_12 | k1_relset_1(A_11, B_12, C_13)=A_11 | ~v1_funct_2(C_13, A_11, B_12) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.57/1.56  tff(c_528, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_502, c_24])).
% 3.57/1.56  tff(c_557, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_492, c_528])).
% 3.57/1.56  tff(c_558, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_493, c_557])).
% 3.57/1.56  tff(c_568, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_558, c_492])).
% 3.57/1.56  tff(c_566, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_558, c_502])).
% 3.57/1.56  tff(c_16, plain, (![C_13, A_11]: (k1_xboole_0=C_13 | ~v1_funct_2(C_13, A_11, k1_xboole_0) | k1_xboole_0=A_11 | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.57/1.56  tff(c_723, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_xboole_0) | k2_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_566, c_16])).
% 3.57/1.56  tff(c_760, plain, (k2_funct_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_568, c_723])).
% 3.57/1.56  tff(c_766, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_760])).
% 3.57/1.56  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.57/1.56  tff(c_28, plain, (![A_15]: (~v1_xboole_0(k2_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.57/1.56  tff(c_133, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_120, c_28])).
% 3.57/1.56  tff(c_137, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_133])).
% 3.57/1.56  tff(c_138, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_137])).
% 3.57/1.56  tff(c_783, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_766, c_138])).
% 3.57/1.56  tff(c_787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_783])).
% 3.57/1.56  tff(c_788, plain, (k2_funct_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_760])).
% 3.57/1.56  tff(c_6, plain, (![A_1]: (k1_relat_1(k2_funct_1(A_1))=k2_relat_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.57/1.56  tff(c_801, plain, (k2_relat_1('#skF_3')=k1_relat_1(k1_xboole_0) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_788, c_6])).
% 3.57/1.56  tff(c_808, plain, (k2_relat_1('#skF_3')=k1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_48, c_40, c_801])).
% 3.57/1.56  tff(c_426, plain, (![A_70, B_71, C_72]: (m1_subset_1(k2_tops_2(A_70, B_71, C_72), k1_zfmisc_1(k2_zfmisc_1(B_71, A_70))) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~v1_funct_2(C_72, A_70, B_71) | ~v1_funct_1(C_72))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.57/1.56  tff(c_10, plain, (![A_5, B_6, C_7]: (k1_relset_1(A_5, B_6, C_7)=k1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.57/1.56  tff(c_504, plain, (![B_79, A_80, C_81]: (k1_relset_1(B_79, A_80, k2_tops_2(A_80, B_79, C_81))=k1_relat_1(k2_tops_2(A_80, B_79, C_81)) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))) | ~v1_funct_2(C_81, A_80, B_79) | ~v1_funct_1(C_81))), inference(resolution, [status(thm)], [c_426, c_10])).
% 3.57/1.56  tff(c_508, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))=k1_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_189, c_504])).
% 3.57/1.56  tff(c_512, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_191, c_490, c_490, c_508])).
% 3.57/1.56  tff(c_692, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_xboole_0, k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_558, c_512])).
% 3.57/1.56  tff(c_793, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_788, c_788, c_692])).
% 3.57/1.56  tff(c_868, plain, (k1_relset_1(k1_relat_1(k1_xboole_0), k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_808, c_793])).
% 3.57/1.56  tff(c_567, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_xboole_0, k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_558, c_493])).
% 3.57/1.56  tff(c_812, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_xboole_0, k1_xboole_0)!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_788, c_567])).
% 3.57/1.56  tff(c_817, plain, (k1_relset_1(k1_relat_1(k1_xboole_0), k1_xboole_0, k1_xboole_0)!=k1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_808, c_808, c_812])).
% 3.57/1.56  tff(c_1033, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_868, c_817])).
% 3.57/1.56  tff(c_1034, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_184])).
% 3.57/1.56  tff(c_1043, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1034, c_138])).
% 3.57/1.56  tff(c_1047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1043])).
% 3.57/1.56  tff(c_1048, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_112])).
% 3.57/1.56  tff(c_1110, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_1057, c_1048])).
% 3.57/1.56  tff(c_1134, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1132, c_1132, c_1132, c_1110])).
% 3.57/1.56  tff(c_1270, plain, (k2_relat_1(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1269, c_1134])).
% 3.57/1.56  tff(c_1304, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1285, c_1270])).
% 3.57/1.56  tff(c_1307, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4, c_1304])).
% 3.57/1.56  tff(c_1311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_48, c_40, c_1307])).
% 3.57/1.56  tff(c_1312, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1131])).
% 3.57/1.56  tff(c_1070, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1057, c_28])).
% 3.57/1.56  tff(c_1074, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1070])).
% 3.57/1.56  tff(c_1075, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_1074])).
% 3.57/1.56  tff(c_1322, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1312, c_1075])).
% 3.57/1.56  tff(c_1326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1322])).
% 3.57/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.56  
% 3.57/1.56  Inference rules
% 3.57/1.56  ----------------------
% 3.57/1.56  #Ref     : 0
% 3.57/1.56  #Sup     : 268
% 3.57/1.56  #Fact    : 0
% 3.57/1.56  #Define  : 0
% 3.57/1.56  #Split   : 6
% 3.57/1.56  #Chain   : 0
% 3.57/1.56  #Close   : 0
% 3.57/1.56  
% 3.57/1.56  Ordering : KBO
% 3.57/1.56  
% 3.57/1.56  Simplification rules
% 3.57/1.56  ----------------------
% 3.57/1.56  #Subsume      : 9
% 3.57/1.56  #Demod        : 416
% 3.57/1.56  #Tautology    : 165
% 3.57/1.56  #SimpNegUnit  : 10
% 3.57/1.56  #BackRed      : 113
% 3.57/1.56  
% 3.57/1.56  #Partial instantiations: 0
% 3.57/1.56  #Strategies tried      : 1
% 3.57/1.56  
% 3.57/1.56  Timing (in seconds)
% 3.57/1.56  ----------------------
% 3.57/1.57  Preprocessing        : 0.33
% 3.57/1.57  Parsing              : 0.17
% 3.57/1.57  CNF conversion       : 0.02
% 3.57/1.57  Main loop            : 0.46
% 3.57/1.57  Inferencing          : 0.15
% 3.57/1.57  Reduction            : 0.16
% 3.57/1.57  Demodulation         : 0.12
% 3.57/1.57  BG Simplification    : 0.02
% 3.57/1.57  Subsumption          : 0.07
% 3.57/1.57  Abstraction          : 0.02
% 3.57/1.57  MUC search           : 0.00
% 3.57/1.57  Cooper               : 0.00
% 3.57/1.57  Total                : 0.84
% 3.57/1.57  Index Insertion      : 0.00
% 3.57/1.57  Index Deletion       : 0.00
% 3.57/1.57  Index Matching       : 0.00
% 3.57/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
