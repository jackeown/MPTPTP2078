%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:26 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  148 (3636 expanded)
%              Number of leaves         :   41 (1307 expanded)
%              Depth                    :   15
%              Number of atoms          :  218 (11265 expanded)
%              Number of equality atoms :   99 (4241 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k3_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

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

tff(f_87,axiom,(
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

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_95,axiom,(
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
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

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

tff(c_114,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_65,c_46])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_117,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_114,c_4])).

tff(c_120,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_117])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_42,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_121,plain,(
    ! [A_40] :
      ( k4_relat_1(A_40) = k2_funct_1(A_40)
      | ~ v2_funct_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_124,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_121])).

tff(c_127,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_50,c_124])).

tff(c_8,plain,(
    ! [A_6] :
      ( k2_relat_1(k4_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_131,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_8])).

tff(c_138,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_131])).

tff(c_632,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_636,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_632])).

tff(c_44,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_109,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_65,c_44])).

tff(c_637,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_109])).

tff(c_48,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_71,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_48])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_71])).

tff(c_646,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_72])).

tff(c_146,plain,(
    ! [A_41,B_42,C_43] :
      ( k1_relset_1(A_41,B_42,C_43) = k1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_150,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_146])).

tff(c_643,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_150])).

tff(c_644,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_114])).

tff(c_877,plain,(
    ! [B_96,A_97,C_98] :
      ( k1_xboole_0 = B_96
      | k1_relset_1(A_97,B_96,C_98) = A_97
      | ~ v1_funct_2(C_98,A_97,B_96)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_892,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_644,c_877])).

tff(c_901,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_643,c_892])).

tff(c_902,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_901])).

tff(c_917,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_902,c_644])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] :
      ( k3_relset_1(A_17,B_18,C_19) = k4_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_669,plain,(
    k3_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_644,c_20])).

tff(c_680,plain,(
    k3_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_669])).

tff(c_915,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_902,c_680])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k3_relset_1(A_8,B_9,C_10),k1_zfmisc_1(k2_zfmisc_1(B_9,A_8)))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_972,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_14])).

tff(c_976,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_972])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] :
      ( k2_relset_1(A_14,B_15,C_16) = k2_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1017,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_976,c_18])).

tff(c_1031,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_1017])).

tff(c_919,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_902,c_646])).

tff(c_642,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_636])).

tff(c_918,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_902,c_642])).

tff(c_1046,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_tops_2(A_102,B_103,C_104) = k2_funct_1(C_104)
      | ~ v2_funct_1(C_104)
      | k2_relset_1(A_102,B_103,C_104) != B_103
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103)))
      | ~ v1_funct_2(C_104,A_102,B_103)
      | ~ v1_funct_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1052,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_917,c_1046])).

tff(c_1061,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_919,c_918,c_42,c_1052])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_relat_1(k4_relat_1(A_6)) = k2_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_134,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_10])).

tff(c_140,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_134])).

tff(c_162,plain,(
    ! [A_45,B_46,C_47] :
      ( k2_relset_1(A_45,B_46,C_47) = k2_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_166,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_162])).

tff(c_167,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_109])).

tff(c_176,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_72])).

tff(c_173,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_150])).

tff(c_174,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_114])).

tff(c_408,plain,(
    ! [B_66,A_67,C_68] :
      ( k1_xboole_0 = B_66
      | k1_relset_1(A_67,B_66,C_68) = A_67
      | ~ v1_funct_2(C_68,A_67,B_66)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_423,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_174,c_408])).

tff(c_433,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_173,c_423])).

tff(c_434,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_433])).

tff(c_199,plain,(
    k3_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_174,c_20])).

tff(c_210,plain,(
    k3_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_199])).

tff(c_446,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_210])).

tff(c_449,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_174])).

tff(c_230,plain,(
    ! [A_57,B_58,C_59] :
      ( m1_subset_1(k3_relset_1(A_57,B_58,C_59),k1_zfmisc_1(k2_zfmisc_1(B_58,A_57)))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_relset_1(A_11,B_12,C_13) = k1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_581,plain,(
    ! [B_72,A_73,C_74] :
      ( k1_relset_1(B_72,A_73,k3_relset_1(A_73,B_72,C_74)) = k1_relat_1(k3_relset_1(A_73,B_72,C_74))
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(resolution,[status(thm)],[c_230,c_16])).

tff(c_585,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) = k1_relat_1(k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_449,c_581])).

tff(c_590,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_446,c_446,c_585])).

tff(c_172,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_166])).

tff(c_450,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_172])).

tff(c_451,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_176])).

tff(c_507,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_tops_2(A_69,B_70,C_71) = k2_funct_1(C_71)
      | ~ v2_funct_1(C_71)
      | k2_relset_1(A_69,B_70,C_71) != B_70
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ v1_funct_2(C_71,A_69,B_70)
      | ~ v1_funct_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_510,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_449,c_507])).

tff(c_516,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_451,c_42,c_510])).

tff(c_599,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_516])).

tff(c_40,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_160,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_66,c_65,c_65,c_66,c_66,c_65,c_65,c_40])).

tff(c_161,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_217,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_167,c_167,c_161])).

tff(c_448,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_434,c_217])).

tff(c_600,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_448])).

tff(c_603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_600])).

tff(c_604,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_77,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(u1_struct_0(A_35))
      | ~ l1_struct_0(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

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

tff(c_175,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_88])).

tff(c_624,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_175])).

tff(c_629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_624])).

tff(c_630,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_696,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_637,c_630])).

tff(c_914,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_902,c_902,c_902,c_696])).

tff(c_1070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1031,c_1061,c_914])).

tff(c_1071,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_901])).

tff(c_645,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_88])).

tff(c_1091,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1071,c_645])).

tff(c_1096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1091])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:11:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.57  
% 3.39/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.57  %$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k3_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.39/1.57  
% 3.39/1.57  %Foreground sorts:
% 3.39/1.57  
% 3.39/1.57  
% 3.39/1.57  %Background operators:
% 3.39/1.57  
% 3.39/1.57  
% 3.39/1.57  %Foreground operators:
% 3.39/1.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.39/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.39/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.39/1.57  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.39/1.57  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.39/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.57  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 3.39/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.39/1.57  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.39/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.39/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.39/1.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.39/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.57  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.39/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.39/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.39/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.39/1.57  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.39/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.39/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.39/1.57  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.39/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.57  
% 3.39/1.60  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.39/1.60  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.39/1.60  tff(f_131, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 3.39/1.60  tff(f_87, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.39/1.60  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.39/1.60  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 3.39/1.60  tff(f_41, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 3.39/1.60  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.39/1.60  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.39/1.60  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.39/1.60  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 3.39/1.60  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 3.39/1.60  tff(f_107, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.39/1.60  tff(f_95, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.39/1.60  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.39/1.60  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.39/1.60  tff(c_56, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.39/1.60  tff(c_58, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.39/1.60  tff(c_66, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_58])).
% 3.39/1.60  tff(c_52, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.39/1.60  tff(c_65, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_58])).
% 3.39/1.60  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.39/1.60  tff(c_114, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_65, c_46])).
% 3.39/1.60  tff(c_4, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.39/1.60  tff(c_117, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_114, c_4])).
% 3.39/1.60  tff(c_120, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_117])).
% 3.39/1.60  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.39/1.60  tff(c_42, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.39/1.60  tff(c_121, plain, (![A_40]: (k4_relat_1(A_40)=k2_funct_1(A_40) | ~v2_funct_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.39/1.60  tff(c_124, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_121])).
% 3.39/1.60  tff(c_127, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_50, c_124])).
% 3.39/1.60  tff(c_8, plain, (![A_6]: (k2_relat_1(k4_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.39/1.60  tff(c_131, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_127, c_8])).
% 3.39/1.60  tff(c_138, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_131])).
% 3.39/1.60  tff(c_632, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.39/1.60  tff(c_636, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_632])).
% 3.39/1.60  tff(c_44, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.39/1.60  tff(c_109, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_65, c_44])).
% 3.39/1.60  tff(c_637, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_636, c_109])).
% 3.39/1.60  tff(c_48, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.39/1.60  tff(c_71, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_48])).
% 3.39/1.60  tff(c_72, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_71])).
% 3.39/1.60  tff(c_646, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_637, c_72])).
% 3.39/1.60  tff(c_146, plain, (![A_41, B_42, C_43]: (k1_relset_1(A_41, B_42, C_43)=k1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.39/1.60  tff(c_150, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_146])).
% 3.39/1.60  tff(c_643, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_637, c_150])).
% 3.39/1.60  tff(c_644, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_637, c_114])).
% 3.39/1.60  tff(c_877, plain, (![B_96, A_97, C_98]: (k1_xboole_0=B_96 | k1_relset_1(A_97, B_96, C_98)=A_97 | ~v1_funct_2(C_98, A_97, B_96) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.39/1.60  tff(c_892, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_644, c_877])).
% 3.39/1.60  tff(c_901, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_646, c_643, c_892])).
% 3.39/1.60  tff(c_902, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_901])).
% 3.39/1.60  tff(c_917, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_902, c_644])).
% 3.39/1.60  tff(c_20, plain, (![A_17, B_18, C_19]: (k3_relset_1(A_17, B_18, C_19)=k4_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.39/1.60  tff(c_669, plain, (k3_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_644, c_20])).
% 3.39/1.60  tff(c_680, plain, (k3_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_669])).
% 3.39/1.60  tff(c_915, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_902, c_680])).
% 3.39/1.60  tff(c_14, plain, (![A_8, B_9, C_10]: (m1_subset_1(k3_relset_1(A_8, B_9, C_10), k1_zfmisc_1(k2_zfmisc_1(B_9, A_8))) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.39/1.60  tff(c_972, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_915, c_14])).
% 3.39/1.60  tff(c_976, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_917, c_972])).
% 3.39/1.60  tff(c_18, plain, (![A_14, B_15, C_16]: (k2_relset_1(A_14, B_15, C_16)=k2_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.39/1.60  tff(c_1017, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_976, c_18])).
% 3.39/1.60  tff(c_1031, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_1017])).
% 3.39/1.60  tff(c_919, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_902, c_646])).
% 3.39/1.60  tff(c_642, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_637, c_636])).
% 3.39/1.60  tff(c_918, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_902, c_642])).
% 3.39/1.60  tff(c_1046, plain, (![A_102, B_103, C_104]: (k2_tops_2(A_102, B_103, C_104)=k2_funct_1(C_104) | ~v2_funct_1(C_104) | k2_relset_1(A_102, B_103, C_104)!=B_103 | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))) | ~v1_funct_2(C_104, A_102, B_103) | ~v1_funct_1(C_104))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.39/1.60  tff(c_1052, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_917, c_1046])).
% 3.39/1.60  tff(c_1061, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_919, c_918, c_42, c_1052])).
% 3.39/1.60  tff(c_10, plain, (![A_6]: (k1_relat_1(k4_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.39/1.60  tff(c_134, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_127, c_10])).
% 3.39/1.60  tff(c_140, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_134])).
% 3.39/1.60  tff(c_162, plain, (![A_45, B_46, C_47]: (k2_relset_1(A_45, B_46, C_47)=k2_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.39/1.60  tff(c_166, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_162])).
% 3.39/1.60  tff(c_167, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_109])).
% 3.39/1.60  tff(c_176, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_72])).
% 3.39/1.60  tff(c_173, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_150])).
% 3.39/1.60  tff(c_174, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_114])).
% 3.39/1.60  tff(c_408, plain, (![B_66, A_67, C_68]: (k1_xboole_0=B_66 | k1_relset_1(A_67, B_66, C_68)=A_67 | ~v1_funct_2(C_68, A_67, B_66) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.39/1.60  tff(c_423, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_174, c_408])).
% 3.39/1.60  tff(c_433, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_173, c_423])).
% 3.39/1.60  tff(c_434, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_433])).
% 3.39/1.60  tff(c_199, plain, (k3_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_174, c_20])).
% 3.39/1.60  tff(c_210, plain, (k3_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_199])).
% 3.39/1.60  tff(c_446, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_434, c_210])).
% 3.39/1.60  tff(c_449, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_434, c_174])).
% 3.39/1.60  tff(c_230, plain, (![A_57, B_58, C_59]: (m1_subset_1(k3_relset_1(A_57, B_58, C_59), k1_zfmisc_1(k2_zfmisc_1(B_58, A_57))) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.39/1.60  tff(c_16, plain, (![A_11, B_12, C_13]: (k1_relset_1(A_11, B_12, C_13)=k1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.39/1.60  tff(c_581, plain, (![B_72, A_73, C_74]: (k1_relset_1(B_72, A_73, k3_relset_1(A_73, B_72, C_74))=k1_relat_1(k3_relset_1(A_73, B_72, C_74)) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(resolution, [status(thm)], [c_230, c_16])).
% 3.39/1.60  tff(c_585, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))=k1_relat_1(k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))), inference(resolution, [status(thm)], [c_449, c_581])).
% 3.39/1.60  tff(c_590, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_446, c_446, c_585])).
% 3.39/1.60  tff(c_172, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_166])).
% 3.39/1.60  tff(c_450, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_434, c_172])).
% 3.39/1.60  tff(c_451, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_434, c_176])).
% 3.39/1.60  tff(c_507, plain, (![A_69, B_70, C_71]: (k2_tops_2(A_69, B_70, C_71)=k2_funct_1(C_71) | ~v2_funct_1(C_71) | k2_relset_1(A_69, B_70, C_71)!=B_70 | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~v1_funct_2(C_71, A_69, B_70) | ~v1_funct_1(C_71))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.39/1.60  tff(c_510, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_449, c_507])).
% 3.39/1.60  tff(c_516, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_451, c_42, c_510])).
% 3.39/1.60  tff(c_599, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_450, c_516])).
% 3.39/1.60  tff(c_40, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.39/1.60  tff(c_160, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_66, c_65, c_65, c_66, c_66, c_65, c_65, c_40])).
% 3.39/1.60  tff(c_161, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_160])).
% 3.39/1.60  tff(c_217, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_167, c_167, c_161])).
% 3.39/1.60  tff(c_448, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_434, c_434, c_217])).
% 3.39/1.60  tff(c_600, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_599, c_448])).
% 3.39/1.60  tff(c_603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_590, c_600])).
% 3.39/1.60  tff(c_604, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_433])).
% 3.39/1.60  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.39/1.60  tff(c_77, plain, (![A_35]: (~v1_xboole_0(u1_struct_0(A_35)) | ~l1_struct_0(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.39/1.60  tff(c_83, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_65, c_77])).
% 3.39/1.60  tff(c_87, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_83])).
% 3.39/1.60  tff(c_88, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_87])).
% 3.39/1.60  tff(c_175, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_88])).
% 3.39/1.60  tff(c_624, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_604, c_175])).
% 3.39/1.60  tff(c_629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_624])).
% 3.39/1.60  tff(c_630, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_160])).
% 3.39/1.60  tff(c_696, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_637, c_637, c_630])).
% 3.39/1.60  tff(c_914, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_902, c_902, c_902, c_696])).
% 3.39/1.60  tff(c_1070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1031, c_1061, c_914])).
% 3.39/1.60  tff(c_1071, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_901])).
% 3.39/1.60  tff(c_645, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_637, c_88])).
% 3.39/1.60  tff(c_1091, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1071, c_645])).
% 3.39/1.60  tff(c_1096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1091])).
% 3.39/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.60  
% 3.39/1.60  Inference rules
% 3.39/1.60  ----------------------
% 3.39/1.60  #Ref     : 0
% 3.39/1.60  #Sup     : 237
% 3.39/1.60  #Fact    : 0
% 3.39/1.60  #Define  : 0
% 3.39/1.60  #Split   : 5
% 3.39/1.60  #Chain   : 0
% 3.39/1.60  #Close   : 0
% 3.39/1.60  
% 3.39/1.60  Ordering : KBO
% 3.39/1.60  
% 3.39/1.60  Simplification rules
% 3.39/1.60  ----------------------
% 3.39/1.60  #Subsume      : 4
% 3.39/1.60  #Demod        : 262
% 3.39/1.60  #Tautology    : 139
% 3.39/1.60  #SimpNegUnit  : 3
% 3.39/1.60  #BackRed      : 100
% 3.39/1.60  
% 3.39/1.60  #Partial instantiations: 0
% 3.39/1.60  #Strategies tried      : 1
% 3.39/1.60  
% 3.39/1.60  Timing (in seconds)
% 3.39/1.60  ----------------------
% 3.69/1.60  Preprocessing        : 0.36
% 3.69/1.60  Parsing              : 0.20
% 3.69/1.60  CNF conversion       : 0.02
% 3.69/1.60  Main loop            : 0.43
% 3.69/1.60  Inferencing          : 0.14
% 3.69/1.60  Reduction            : 0.15
% 3.69/1.60  Demodulation         : 0.11
% 3.69/1.60  BG Simplification    : 0.02
% 3.69/1.60  Subsumption          : 0.07
% 3.69/1.60  Abstraction          : 0.03
% 3.69/1.60  MUC search           : 0.00
% 3.69/1.60  Cooper               : 0.00
% 3.69/1.60  Total                : 0.85
% 3.69/1.60  Index Insertion      : 0.00
% 3.69/1.60  Index Deletion       : 0.00
% 3.69/1.60  Index Matching       : 0.00
% 3.69/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
