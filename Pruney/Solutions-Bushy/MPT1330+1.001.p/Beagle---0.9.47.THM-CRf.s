%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1330+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:48 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  137 (1147 expanded)
%              Number of leaves         :   36 ( 402 expanded)
%              Depth                    :   18
%              Number of atoms          :  195 (2974 expanded)
%              Number of equality atoms :   71 (1191 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_109,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_52,axiom,(
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

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(c_8,plain,(
    ! [B_5] : r1_tarski(B_5,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_75,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_54,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_57,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_65,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_57])).

tff(c_52,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_64,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_57])).

tff(c_48,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_66,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_48])).

tff(c_77,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_66])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_64,c_46])).

tff(c_181,plain,(
    ! [A_67,B_68,C_69] :
      ( k1_relset_1(A_67,B_68,C_69) = k1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_190,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_181])).

tff(c_563,plain,(
    ! [B_129,A_130,C_131] :
      ( k1_xboole_0 = B_129
      | k1_relset_1(A_130,B_129,C_131) = A_130
      | ~ v1_funct_2(C_131,A_130,B_129)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_130,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_578,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_563])).

tff(c_584,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_190,c_578])).

tff(c_585,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_584])).

tff(c_107,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_116,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_107])).

tff(c_34,plain,(
    ! [A_27] :
      ( k10_relat_1(A_27,k2_relat_1(A_27)) = k1_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_416,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( k8_relset_1(A_110,B_111,C_112,D_113) = k10_relat_1(C_112,D_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_431,plain,(
    ! [D_113] : k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_113) = k10_relat_1('#skF_3',D_113) ),
    inference(resolution,[status(thm)],[c_76,c_416])).

tff(c_314,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( m1_subset_1(k8_relset_1(A_91,B_92,C_93,D_94),k1_zfmisc_1(A_91))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_338,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( r1_tarski(k8_relset_1(A_95,B_96,C_97,D_98),A_95)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(resolution,[status(thm)],[c_314,c_38])).

tff(c_353,plain,(
    ! [D_98] : r1_tarski(k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_98),k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_76,c_338])).

tff(c_470,plain,(
    ! [D_117] : r1_tarski(k10_relat_1('#skF_3',D_117),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_353])).

tff(c_476,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_470])).

tff(c_479,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_476])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( B_5 = A_4
      | ~ r1_tarski(B_5,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_482,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_1'),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_479,c_4])).

tff(c_501,plain,(
    ~ r1_tarski(k2_struct_0('#skF_1'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_482])).

tff(c_587,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_501])).

tff(c_603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_587])).

tff(c_604,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_482])).

tff(c_42,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_117,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_64,c_42])).

tff(c_434,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_117])).

tff(c_608,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_434])).

tff(c_130,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_relset_1(A_54,B_55,C_56) = k2_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_139,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_130])).

tff(c_215,plain,(
    ! [A_75,B_76,C_77] :
      ( m1_subset_1(k2_relset_1(A_75,B_76,C_77),k1_zfmisc_1(B_76))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_236,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_215])).

tff(c_242,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_236])).

tff(c_246,plain,(
    r1_tarski(k2_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_242,c_38])).

tff(c_477,plain,(
    ! [D_117] :
      ( k10_relat_1('#skF_3',D_117) = k2_struct_0('#skF_1')
      | ~ r1_tarski(k2_struct_0('#skF_1'),k10_relat_1('#skF_3',D_117)) ) ),
    inference(resolution,[status(thm)],[c_470,c_4])).

tff(c_807,plain,(
    ! [D_143] :
      ( k10_relat_1('#skF_3',D_143) = k1_relat_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',D_143)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_604,c_477])).

tff(c_811,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_807])).

tff(c_813,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_8,c_811])).

tff(c_36,plain,(
    ! [C_30,A_28,B_29] :
      ( r1_tarski(k10_relat_1(C_30,A_28),k10_relat_1(C_30,B_29))
      | ~ r1_tarski(A_28,B_29)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_824,plain,(
    ! [B_29] :
      ( r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',B_29))
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_29)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_813,c_36])).

tff(c_852,plain,(
    ! [B_144] :
      ( r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',B_144))
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_824])).

tff(c_806,plain,(
    ! [D_117] :
      ( k10_relat_1('#skF_3',D_117) = k1_relat_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',D_117)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_604,c_477])).

tff(c_873,plain,(
    ! [B_145] :
      ( k10_relat_1('#skF_3',B_145) = k1_relat_1('#skF_3')
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_145) ) ),
    inference(resolution,[status(thm)],[c_852,c_806])).

tff(c_876,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_246,c_873])).

tff(c_884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_608,c_876])).

tff(c_886,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_892,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_64])).

tff(c_885,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_887,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_65])).

tff(c_912,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_887,c_46])).

tff(c_1080,plain,(
    ! [A_185,B_186,C_187,D_188] :
      ( k8_relset_1(A_185,B_186,C_187,D_188) = k10_relat_1(C_187,D_188)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1090,plain,(
    ! [D_188] : k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',D_188) = k10_relat_1('#skF_3',D_188) ),
    inference(resolution,[status(thm)],[c_912,c_1080])).

tff(c_946,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_887,c_886,c_885,c_42])).

tff(c_1092,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1090,c_946])).

tff(c_1004,plain,(
    ! [A_172,B_173,C_174] :
      ( k2_relset_1(A_172,B_173,C_174) = k2_relat_1(C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1012,plain,(
    k2_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_912,c_1004])).

tff(c_1044,plain,(
    ! [A_182,B_183,C_184] :
      ( m1_subset_1(k2_relset_1(A_182,B_183,C_184),k1_zfmisc_1(B_183))
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1065,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1012,c_1044])).

tff(c_1071,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_1065])).

tff(c_1075,plain,(
    r1_tarski(k2_relat_1('#skF_3'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1071,c_38])).

tff(c_936,plain,(
    ! [C_153,A_154,B_155] :
      ( v1_relat_1(C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_944,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_912,c_936])).

tff(c_906,plain,(
    v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_886,c_66])).

tff(c_970,plain,(
    ! [A_164,B_165,C_166] :
      ( k1_relset_1(A_164,B_165,C_166) = k1_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_978,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_912,c_970])).

tff(c_1208,plain,(
    ! [B_202,C_203] :
      ( k1_relset_1(k1_xboole_0,B_202,C_203) = k1_xboole_0
      | ~ v1_funct_2(C_203,k1_xboole_0,B_202)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1219,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3') = k1_xboole_0
    | ~ v1_funct_2('#skF_3',k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_912,c_1208])).

tff(c_1228,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_906,c_978,c_1219])).

tff(c_1102,plain,(
    ! [A_190,B_191,C_192,D_193] :
      ( m1_subset_1(k8_relset_1(A_190,B_191,C_192,D_193),k1_zfmisc_1(A_190))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1123,plain,(
    ! [D_188] :
      ( m1_subset_1(k10_relat_1('#skF_3',D_188),k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1090,c_1102])).

tff(c_1131,plain,(
    ! [D_194] : m1_subset_1(k10_relat_1('#skF_3',D_194),k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_1123])).

tff(c_1142,plain,(
    ! [D_195] : r1_tarski(k10_relat_1('#skF_3',D_195),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1131,c_38])).

tff(c_1148,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1142])).

tff(c_1151,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_1148])).

tff(c_1154,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1151,c_4])).

tff(c_1160,plain,(
    ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1154])).

tff(c_1230,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1228,c_1160])).

tff(c_1236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1230])).

tff(c_1237,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1154])).

tff(c_1280,plain,(
    ! [D_206] :
      ( k10_relat_1('#skF_3',D_206) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k10_relat_1('#skF_3',D_206)) ) ),
    inference(resolution,[status(thm)],[c_1142,c_4])).

tff(c_1284,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1280])).

tff(c_1286,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_8,c_1237,c_1284])).

tff(c_1297,plain,(
    ! [B_29] :
      ( r1_tarski(k1_xboole_0,k10_relat_1('#skF_3',B_29))
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_29)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1286,c_36])).

tff(c_1322,plain,(
    ! [B_207] :
      ( r1_tarski(k1_xboole_0,k10_relat_1('#skF_3',B_207))
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_1297])).

tff(c_1330,plain,(
    r1_tarski(k1_xboole_0,k10_relat_1('#skF_3',k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1075,c_1322])).

tff(c_1149,plain,(
    ! [D_195] :
      ( k10_relat_1('#skF_3',D_195) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k10_relat_1('#skF_3',D_195)) ) ),
    inference(resolution,[status(thm)],[c_1142,c_4])).

tff(c_1335,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1330,c_1149])).

tff(c_1341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1092,c_1335])).

%------------------------------------------------------------------------------
