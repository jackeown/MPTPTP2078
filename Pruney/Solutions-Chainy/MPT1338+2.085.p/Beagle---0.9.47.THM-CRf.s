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
% DateTime   : Thu Dec  3 10:23:26 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  152 (3446 expanded)
%              Number of leaves         :   41 (1241 expanded)
%              Depth                    :   16
%              Number of atoms          :  236 (10695 expanded)
%              Number of equality atoms :   99 (4018 expanded)
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

tff(f_135,negated_conjecture,(
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

tff(f_91,axiom,(
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

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_87,axiom,(
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

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_99,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_58,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_66,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_58])).

tff(c_52,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_65,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_58])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_96,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_65,c_46])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_99,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_96,c_4])).

tff(c_102,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_99])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_42,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_10,plain,(
    ! [A_7] :
      ( k2_relat_1(k2_funct_1(A_7)) = k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_542,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_546,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_542])).

tff(c_44,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_91,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_65,c_44])).

tff(c_547,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_91])).

tff(c_48,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_71,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_48])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_71])).

tff(c_556,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_72])).

tff(c_554,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_96])).

tff(c_598,plain,(
    ! [A_79,B_80,C_81] :
      ( k1_relset_1(A_79,B_80,C_81) = k1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_602,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_554,c_598])).

tff(c_818,plain,(
    ! [B_97,A_98,C_99] :
      ( k1_xboole_0 = B_97
      | k1_relset_1(A_98,B_97,C_99) = A_98
      | ~ v1_funct_2(C_99,A_98,B_97)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_830,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_554,c_818])).

tff(c_838,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_602,c_830])).

tff(c_839,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_838])).

tff(c_513,plain,(
    ! [A_69] :
      ( k4_relat_1(A_69) = k2_funct_1(A_69)
      | ~ v2_funct_1(A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_516,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_513])).

tff(c_519,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_50,c_516])).

tff(c_588,plain,(
    ! [A_76,B_77,C_78] :
      ( k3_relset_1(A_76,B_77,C_78) = k4_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_591,plain,(
    k3_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_554,c_588])).

tff(c_593,plain,(
    k3_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_591])).

tff(c_852,plain,(
    k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_593])).

tff(c_854,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_554])).

tff(c_614,plain,(
    ! [A_86,B_87,C_88] :
      ( m1_subset_1(k3_relset_1(A_86,B_87,C_88),k1_zfmisc_1(k2_zfmisc_1(B_87,A_86)))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] :
      ( k2_relset_1(A_14,B_15,C_16) = k2_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_985,plain,(
    ! [B_103,A_104,C_105] :
      ( k2_relset_1(B_103,A_104,k3_relset_1(A_104,B_103,C_105)) = k2_relat_1(k3_relset_1(A_104,B_103,C_105))
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103))) ) ),
    inference(resolution,[status(thm)],[c_614,c_18])).

tff(c_989,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) = k2_relat_1(k3_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_854,c_985])).

tff(c_994,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_852,c_852,c_989])).

tff(c_855,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_556])).

tff(c_552,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_546])).

tff(c_853,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_552])).

tff(c_38,plain,(
    ! [A_25,B_26,C_27] :
      ( k2_tops_2(A_25,B_26,C_27) = k2_funct_1(C_27)
      | ~ v2_funct_1(C_27)
      | k2_relset_1(A_25,B_26,C_27) != B_26
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_2(C_27,A_25,B_26)
      | ~ v1_funct_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_890,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_854,c_38])).

tff(c_914,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_855,c_853,c_42,c_890])).

tff(c_12,plain,(
    ! [A_7] :
      ( k1_relat_1(k2_funct_1(A_7)) = k2_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_154,plain,(
    ! [A_48,B_49,C_50] :
      ( k2_relset_1(A_48,B_49,C_50) = k2_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_158,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_154])).

tff(c_159,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_91])).

tff(c_170,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_72])).

tff(c_134,plain,(
    ! [A_41,B_42,C_43] :
      ( k1_relset_1(A_41,B_42,C_43) = k1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_138,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_134])).

tff(c_167,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_138])).

tff(c_168,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_96])).

tff(c_315,plain,(
    ! [B_60,A_61,C_62] :
      ( k1_xboole_0 = B_60
      | k1_relset_1(A_61,B_60,C_62) = A_61
      | ~ v1_funct_2(C_62,A_61,B_60)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_327,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_168,c_315])).

tff(c_334,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_167,c_327])).

tff(c_335,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_334])).

tff(c_105,plain,(
    ! [A_38] :
      ( k4_relat_1(A_38) = k2_funct_1(A_38)
      | ~ v2_funct_1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_108,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_105])).

tff(c_111,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_50,c_108])).

tff(c_143,plain,(
    ! [A_44,B_45,C_46] :
      ( k3_relset_1(A_44,B_45,C_46) = k4_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_146,plain,(
    k3_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_143])).

tff(c_148,plain,(
    k3_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_146])).

tff(c_166,plain,(
    k3_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_148])).

tff(c_223,plain,(
    ! [A_57,B_58,C_59] :
      ( m1_subset_1(k3_relset_1(A_57,B_58,C_59),k1_zfmisc_1(k2_zfmisc_1(B_58,A_57)))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_250,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_223])).

tff(c_261,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_250])).

tff(c_340,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_261])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_relset_1(A_11,B_12,C_13) = k1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_440,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_340,c_16])).

tff(c_346,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_170])).

tff(c_164,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_158])).

tff(c_345,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_164])).

tff(c_344,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_168])).

tff(c_463,plain,(
    ! [A_66,B_67,C_68] :
      ( k2_tops_2(A_66,B_67,C_68) = k2_funct_1(C_68)
      | ~ v2_funct_1(C_68)
      | k2_relset_1(A_66,B_67,C_68) != B_67
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ v1_funct_2(C_68,A_66,B_67)
      | ~ v1_funct_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_469,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_344,c_463])).

tff(c_477,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_346,c_345,c_42,c_469])).

tff(c_40,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_103,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_66,c_65,c_65,c_66,c_66,c_65,c_65,c_40])).

tff(c_104,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_165,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_159,c_159,c_104])).

tff(c_341,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_335,c_165])).

tff(c_479,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_341])).

tff(c_480,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_479])).

tff(c_487,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_480])).

tff(c_491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_50,c_42,c_487])).

tff(c_492,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_334])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_77,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(u1_struct_0(A_35))
      | ~ l1_struct_0(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

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

tff(c_169,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_88])).

tff(c_506,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_169])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_506])).

tff(c_511,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_553,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_547,c_511])).

tff(c_849,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_839,c_839,c_553])).

tff(c_1002,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_994,c_914,c_849])).

tff(c_1005,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1002])).

tff(c_1009,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_50,c_42,c_1005])).

tff(c_1010,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_838])).

tff(c_555,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_88])).

tff(c_1029,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_555])).

tff(c_1033,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1029])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:44:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.48  
% 3.12/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.48  %$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k3_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.12/1.48  
% 3.12/1.48  %Foreground sorts:
% 3.12/1.48  
% 3.12/1.48  
% 3.12/1.48  %Background operators:
% 3.12/1.48  
% 3.12/1.48  
% 3.12/1.48  %Foreground operators:
% 3.12/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.12/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.12/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.12/1.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.12/1.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.12/1.48  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 3.12/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.12/1.48  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.12/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.12/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.12/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.12/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.12/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.12/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.12/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.12/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.12/1.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.12/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.12/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.12/1.48  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.12/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.12/1.48  
% 3.26/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.26/1.50  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.26/1.50  tff(f_135, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 3.26/1.50  tff(f_91, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.26/1.50  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.26/1.50  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.26/1.50  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.26/1.50  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.26/1.50  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.26/1.50  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 3.26/1.50  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 3.26/1.50  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 3.26/1.50  tff(f_111, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.26/1.50  tff(f_99, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.26/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.26/1.50  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.50  tff(c_56, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.26/1.50  tff(c_58, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.26/1.50  tff(c_66, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_58])).
% 3.26/1.50  tff(c_52, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.26/1.50  tff(c_65, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_58])).
% 3.26/1.50  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.26/1.50  tff(c_96, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_65, c_46])).
% 3.26/1.50  tff(c_4, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.50  tff(c_99, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_96, c_4])).
% 3.26/1.50  tff(c_102, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_99])).
% 3.26/1.50  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.26/1.50  tff(c_42, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.26/1.50  tff(c_10, plain, (![A_7]: (k2_relat_1(k2_funct_1(A_7))=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.26/1.50  tff(c_542, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.26/1.50  tff(c_546, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_542])).
% 3.26/1.50  tff(c_44, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.26/1.50  tff(c_91, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_65, c_44])).
% 3.26/1.50  tff(c_547, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_546, c_91])).
% 3.26/1.50  tff(c_48, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.26/1.50  tff(c_71, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_48])).
% 3.26/1.50  tff(c_72, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_71])).
% 3.26/1.50  tff(c_556, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_547, c_72])).
% 3.26/1.50  tff(c_554, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_547, c_96])).
% 3.26/1.50  tff(c_598, plain, (![A_79, B_80, C_81]: (k1_relset_1(A_79, B_80, C_81)=k1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.26/1.50  tff(c_602, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_554, c_598])).
% 3.26/1.50  tff(c_818, plain, (![B_97, A_98, C_99]: (k1_xboole_0=B_97 | k1_relset_1(A_98, B_97, C_99)=A_98 | ~v1_funct_2(C_99, A_98, B_97) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.26/1.50  tff(c_830, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_554, c_818])).
% 3.26/1.50  tff(c_838, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_556, c_602, c_830])).
% 3.26/1.50  tff(c_839, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_838])).
% 3.26/1.50  tff(c_513, plain, (![A_69]: (k4_relat_1(A_69)=k2_funct_1(A_69) | ~v2_funct_1(A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.26/1.50  tff(c_516, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_513])).
% 3.26/1.50  tff(c_519, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_50, c_516])).
% 3.26/1.50  tff(c_588, plain, (![A_76, B_77, C_78]: (k3_relset_1(A_76, B_77, C_78)=k4_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.26/1.50  tff(c_591, plain, (k3_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_554, c_588])).
% 3.26/1.50  tff(c_593, plain, (k3_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_519, c_591])).
% 3.26/1.50  tff(c_852, plain, (k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_839, c_593])).
% 3.26/1.50  tff(c_854, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_839, c_554])).
% 3.26/1.50  tff(c_614, plain, (![A_86, B_87, C_88]: (m1_subset_1(k3_relset_1(A_86, B_87, C_88), k1_zfmisc_1(k2_zfmisc_1(B_87, A_86))) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.26/1.50  tff(c_18, plain, (![A_14, B_15, C_16]: (k2_relset_1(A_14, B_15, C_16)=k2_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.26/1.50  tff(c_985, plain, (![B_103, A_104, C_105]: (k2_relset_1(B_103, A_104, k3_relset_1(A_104, B_103, C_105))=k2_relat_1(k3_relset_1(A_104, B_103, C_105)) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))))), inference(resolution, [status(thm)], [c_614, c_18])).
% 3.26/1.50  tff(c_989, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))=k2_relat_1(k3_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))), inference(resolution, [status(thm)], [c_854, c_985])).
% 3.26/1.50  tff(c_994, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_852, c_852, c_989])).
% 3.26/1.50  tff(c_855, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_839, c_556])).
% 3.26/1.50  tff(c_552, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_547, c_546])).
% 3.26/1.50  tff(c_853, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_839, c_552])).
% 3.26/1.50  tff(c_38, plain, (![A_25, B_26, C_27]: (k2_tops_2(A_25, B_26, C_27)=k2_funct_1(C_27) | ~v2_funct_1(C_27) | k2_relset_1(A_25, B_26, C_27)!=B_26 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_2(C_27, A_25, B_26) | ~v1_funct_1(C_27))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.26/1.50  tff(c_890, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_854, c_38])).
% 3.26/1.50  tff(c_914, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_855, c_853, c_42, c_890])).
% 3.26/1.50  tff(c_12, plain, (![A_7]: (k1_relat_1(k2_funct_1(A_7))=k2_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.26/1.50  tff(c_154, plain, (![A_48, B_49, C_50]: (k2_relset_1(A_48, B_49, C_50)=k2_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.26/1.50  tff(c_158, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_154])).
% 3.26/1.50  tff(c_159, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_91])).
% 3.26/1.50  tff(c_170, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_72])).
% 3.26/1.50  tff(c_134, plain, (![A_41, B_42, C_43]: (k1_relset_1(A_41, B_42, C_43)=k1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.26/1.50  tff(c_138, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_134])).
% 3.26/1.50  tff(c_167, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_138])).
% 3.26/1.50  tff(c_168, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_96])).
% 3.26/1.50  tff(c_315, plain, (![B_60, A_61, C_62]: (k1_xboole_0=B_60 | k1_relset_1(A_61, B_60, C_62)=A_61 | ~v1_funct_2(C_62, A_61, B_60) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.26/1.50  tff(c_327, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_168, c_315])).
% 3.26/1.50  tff(c_334, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_167, c_327])).
% 3.26/1.50  tff(c_335, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_334])).
% 3.26/1.50  tff(c_105, plain, (![A_38]: (k4_relat_1(A_38)=k2_funct_1(A_38) | ~v2_funct_1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.26/1.50  tff(c_108, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_105])).
% 3.26/1.50  tff(c_111, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_50, c_108])).
% 3.26/1.50  tff(c_143, plain, (![A_44, B_45, C_46]: (k3_relset_1(A_44, B_45, C_46)=k4_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.26/1.50  tff(c_146, plain, (k3_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_143])).
% 3.26/1.50  tff(c_148, plain, (k3_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_146])).
% 3.26/1.50  tff(c_166, plain, (k3_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_148])).
% 3.26/1.50  tff(c_223, plain, (![A_57, B_58, C_59]: (m1_subset_1(k3_relset_1(A_57, B_58, C_59), k1_zfmisc_1(k2_zfmisc_1(B_58, A_57))) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.26/1.50  tff(c_250, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_166, c_223])).
% 3.26/1.50  tff(c_261, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_250])).
% 3.26/1.50  tff(c_340, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_261])).
% 3.26/1.50  tff(c_16, plain, (![A_11, B_12, C_13]: (k1_relset_1(A_11, B_12, C_13)=k1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.26/1.50  tff(c_440, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_340, c_16])).
% 3.26/1.50  tff(c_346, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_170])).
% 3.26/1.50  tff(c_164, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_158])).
% 3.26/1.50  tff(c_345, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_164])).
% 3.26/1.50  tff(c_344, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_335, c_168])).
% 3.26/1.50  tff(c_463, plain, (![A_66, B_67, C_68]: (k2_tops_2(A_66, B_67, C_68)=k2_funct_1(C_68) | ~v2_funct_1(C_68) | k2_relset_1(A_66, B_67, C_68)!=B_67 | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~v1_funct_2(C_68, A_66, B_67) | ~v1_funct_1(C_68))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.26/1.50  tff(c_469, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_344, c_463])).
% 3.26/1.50  tff(c_477, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_346, c_345, c_42, c_469])).
% 3.26/1.50  tff(c_40, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.26/1.50  tff(c_103, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_66, c_65, c_65, c_66, c_66, c_65, c_65, c_40])).
% 3.26/1.50  tff(c_104, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_103])).
% 3.26/1.50  tff(c_165, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_159, c_159, c_104])).
% 3.26/1.50  tff(c_341, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_335, c_165])).
% 3.26/1.50  tff(c_479, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_477, c_341])).
% 3.26/1.50  tff(c_480, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_440, c_479])).
% 3.26/1.50  tff(c_487, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_480])).
% 3.26/1.50  tff(c_491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_50, c_42, c_487])).
% 3.26/1.50  tff(c_492, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_334])).
% 3.26/1.50  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.26/1.50  tff(c_77, plain, (![A_35]: (~v1_xboole_0(u1_struct_0(A_35)) | ~l1_struct_0(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.26/1.50  tff(c_83, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_65, c_77])).
% 3.26/1.50  tff(c_87, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_83])).
% 3.26/1.50  tff(c_88, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_87])).
% 3.26/1.50  tff(c_169, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_88])).
% 3.26/1.50  tff(c_506, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_492, c_169])).
% 3.26/1.50  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_506])).
% 3.26/1.50  tff(c_511, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_103])).
% 3.26/1.50  tff(c_553, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_547, c_547, c_511])).
% 3.26/1.50  tff(c_849, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_839, c_839, c_839, c_553])).
% 3.26/1.50  tff(c_1002, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_994, c_914, c_849])).
% 3.26/1.50  tff(c_1005, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_1002])).
% 3.26/1.50  tff(c_1009, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_50, c_42, c_1005])).
% 3.26/1.50  tff(c_1010, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_838])).
% 3.26/1.50  tff(c_555, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_547, c_88])).
% 3.26/1.50  tff(c_1029, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_555])).
% 3.26/1.50  tff(c_1033, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1029])).
% 3.26/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.50  
% 3.26/1.50  Inference rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Ref     : 0
% 3.26/1.50  #Sup     : 222
% 3.26/1.50  #Fact    : 0
% 3.26/1.50  #Define  : 0
% 3.26/1.50  #Split   : 6
% 3.26/1.50  #Chain   : 0
% 3.26/1.50  #Close   : 0
% 3.26/1.50  
% 3.26/1.50  Ordering : KBO
% 3.26/1.50  
% 3.26/1.50  Simplification rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Subsume      : 4
% 3.26/1.50  #Demod        : 250
% 3.26/1.50  #Tautology    : 135
% 3.26/1.50  #SimpNegUnit  : 5
% 3.26/1.50  #BackRed      : 101
% 3.26/1.50  
% 3.26/1.50  #Partial instantiations: 0
% 3.26/1.50  #Strategies tried      : 1
% 3.26/1.50  
% 3.26/1.50  Timing (in seconds)
% 3.26/1.50  ----------------------
% 3.26/1.50  Preprocessing        : 0.34
% 3.26/1.50  Parsing              : 0.18
% 3.26/1.50  CNF conversion       : 0.02
% 3.26/1.50  Main loop            : 0.39
% 3.26/1.50  Inferencing          : 0.13
% 3.26/1.50  Reduction            : 0.14
% 3.26/1.51  Demodulation         : 0.10
% 3.26/1.51  BG Simplification    : 0.02
% 3.26/1.51  Subsumption          : 0.06
% 3.26/1.51  Abstraction          : 0.02
% 3.26/1.51  MUC search           : 0.00
% 3.26/1.51  Cooper               : 0.00
% 3.26/1.51  Total                : 0.77
% 3.26/1.51  Index Insertion      : 0.00
% 3.26/1.51  Index Deletion       : 0.00
% 3.26/1.51  Index Matching       : 0.00
% 3.26/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
