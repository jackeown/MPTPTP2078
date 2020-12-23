%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:19 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  156 (7505 expanded)
%              Number of leaves         :   40 (2686 expanded)
%              Depth                    :   22
%              Number of atoms          :  233 (23138 expanded)
%              Number of equality atoms :  105 (8307 expanded)
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

tff(f_82,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_78,axiom,(
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
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_55,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

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

tff(c_104,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_62,c_44])).

tff(c_155,plain,(
    ! [A_42,B_43,C_44] :
      ( k2_relset_1(A_42,B_43,C_44) = k2_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_159,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_155])).

tff(c_42,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_110,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_62,c_42])).

tff(c_160,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_110])).

tff(c_529,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_104])).

tff(c_105,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_109,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_105])).

tff(c_40,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_115,plain,(
    ! [A_37] :
      ( k4_relat_1(A_37) = k2_funct_1(A_37)
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_118,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_115])).

tff(c_121,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_48,c_118])).

tff(c_144,plain,(
    ! [A_38,B_39,C_40] :
      ( k3_relset_1(A_38,B_39,C_40) = k4_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_147,plain,(
    k3_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_144])).

tff(c_149,plain,(
    k3_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_147])).

tff(c_528,plain,(
    k3_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_149])).

tff(c_587,plain,(
    ! [A_74,B_75,C_76] :
      ( m1_subset_1(k3_relset_1(A_74,B_75,C_76),k1_zfmisc_1(k2_zfmisc_1(B_75,A_74)))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_606,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_587])).

tff(c_613,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_606])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_631,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_613,c_10])).

tff(c_4,plain,(
    ! [A_1] :
      ( k2_relat_1(k4_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_4])).

tff(c_134,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_128])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_1] :
      ( k1_relat_1(k4_relat_1(A_1)) = k2_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] :
      ( k3_relset_1(A_15,B_16,C_17) = k4_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_630,plain,(
    k3_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k4_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_613,c_18])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8] :
      ( m1_subset_1(k3_relset_1(A_6,B_7,C_8),k1_zfmisc_1(k2_zfmisc_1(B_7,A_6)))
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_643,plain,
    ( m1_subset_1(k4_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_12])).

tff(c_647,plain,(
    m1_subset_1(k4_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_643])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( k1_relset_1(A_9,B_10,C_11) = k1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_661,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k4_relat_1(k2_funct_1('#skF_3'))) = k1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_647,c_14])).

tff(c_801,plain,(
    ! [B_87,C_88,A_89] :
      ( k1_xboole_0 = B_87
      | v1_funct_2(C_88,A_89,B_87)
      | k1_relset_1(A_89,B_87,C_88) != A_89
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_810,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_funct_2(k4_relat_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k4_relat_1(k2_funct_1('#skF_3'))) != k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_647,c_801])).

tff(c_824,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_funct_2(k4_relat_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | k1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_810])).

tff(c_842,plain,(
    k1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_824])).

tff(c_845,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_842])).

tff(c_847,plain,(
    k2_struct_0('#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_134,c_845])).

tff(c_46,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_72,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_62,c_46])).

tff(c_531,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_72])).

tff(c_560,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_529,c_14])).

tff(c_876,plain,(
    ! [B_90,A_91,C_92] :
      ( k1_xboole_0 = B_90
      | k1_relset_1(A_91,B_90,C_92) = A_91
      | ~ v1_funct_2(C_92,A_91,B_90)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_897,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_529,c_876])).

tff(c_911,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_560,c_897])).

tff(c_912,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_847,c_911])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_82,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(u1_struct_0(A_32))
      | ~ l1_struct_0(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_88,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_82])).

tff(c_92,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_88])).

tff(c_93,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_92])).

tff(c_530,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_93])).

tff(c_939,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_912,c_530])).

tff(c_944,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_939])).

tff(c_946,plain,(
    k1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_824])).

tff(c_951,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_946,c_6])).

tff(c_958,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_134,c_951])).

tff(c_984,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_531])).

tff(c_527,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_159])).

tff(c_982,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_527])).

tff(c_983,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_529])).

tff(c_1075,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_tops_2(A_96,B_97,C_98) = k2_funct_1(C_98)
      | ~ v2_funct_1(C_98)
      | k2_relset_1(A_96,B_97,C_98) != B_97
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_2(C_98,A_96,B_97)
      | ~ v1_funct_1(C_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1078,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_983,c_1075])).

tff(c_1084,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_984,c_982,c_40,c_1078])).

tff(c_171,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_72])).

tff(c_169,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_104])).

tff(c_204,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_169,c_14])).

tff(c_348,plain,(
    ! [B_63,A_64,C_65] :
      ( k1_xboole_0 = B_63
      | k1_relset_1(A_64,B_63,C_65) = A_64
      | ~ v1_funct_2(C_65,A_64,B_63)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_360,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_169,c_348])).

tff(c_367,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_204,c_360])).

tff(c_368,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_380,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_171])).

tff(c_167,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_159])).

tff(c_377,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_167])).

tff(c_378,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_169])).

tff(c_447,plain,(
    ! [A_66,B_67,C_68] :
      ( k2_tops_2(A_66,B_67,C_68) = k2_funct_1(C_68)
      | ~ v2_funct_1(C_68)
      | k2_relset_1(A_66,B_67,C_68) != B_67
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ v1_funct_2(C_68,A_66,B_67)
      | ~ v1_funct_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_450,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_378,c_447])).

tff(c_456,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_380,c_377,c_40,c_450])).

tff(c_38,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_165,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_63,c_62,c_62,c_63,c_63,c_62,c_62,c_38])).

tff(c_166,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_218,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_160,c_160,c_166])).

tff(c_375,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_368,c_218])).

tff(c_498,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_375])).

tff(c_125,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_6])).

tff(c_132,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_125])).

tff(c_168,plain,(
    k3_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_149])).

tff(c_223,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1(k3_relset_1(A_54,B_55,C_56),k1_zfmisc_1(k2_zfmisc_1(B_55,A_54)))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_250,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_223])).

tff(c_259,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_250])).

tff(c_374,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_259])).

tff(c_477,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_374,c_14])).

tff(c_492,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_477])).

tff(c_503,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_498,c_492])).

tff(c_504,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_170,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_93])).

tff(c_519,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_170])).

tff(c_524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_519])).

tff(c_525,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_581,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_160,c_525])).

tff(c_979,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_958,c_958,c_581])).

tff(c_1139,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_979])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] :
      ( k2_relset_1(A_12,B_13,C_14) = k2_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_619,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_613,c_16])).

tff(c_629,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_619])).

tff(c_975,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_629])).

tff(c_1140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1139,c_975])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.73  
% 3.61/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.73  %$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k3_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.61/1.73  
% 3.61/1.73  %Foreground sorts:
% 3.61/1.73  
% 3.61/1.73  
% 3.61/1.73  %Background operators:
% 3.61/1.73  
% 3.61/1.73  
% 3.61/1.73  %Foreground operators:
% 3.61/1.73  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.61/1.73  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.61/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.61/1.73  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.61/1.73  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.61/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.61/1.73  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 3.61/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.61/1.73  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.61/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.61/1.73  tff('#skF_2', type, '#skF_2': $i).
% 3.61/1.73  tff('#skF_3', type, '#skF_3': $i).
% 3.61/1.73  tff('#skF_1', type, '#skF_1': $i).
% 3.61/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.61/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.61/1.73  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.61/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.61/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.61/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.61/1.73  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.61/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.61/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.61/1.73  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.61/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.61/1.73  
% 3.61/1.76  tff(f_126, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 3.61/1.76  tff(f_82, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.61/1.76  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.61/1.76  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.61/1.76  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 3.61/1.76  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 3.61/1.76  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 3.61/1.76  tff(f_32, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 3.61/1.76  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.61/1.76  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.61/1.76  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.61/1.76  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.61/1.76  tff(f_102, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.61/1.76  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.61/1.76  tff(c_54, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.61/1.76  tff(c_55, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.61/1.76  tff(c_63, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_55])).
% 3.61/1.76  tff(c_50, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.61/1.76  tff(c_62, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_55])).
% 3.61/1.76  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.61/1.76  tff(c_104, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_62, c_44])).
% 3.61/1.76  tff(c_155, plain, (![A_42, B_43, C_44]: (k2_relset_1(A_42, B_43, C_44)=k2_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.61/1.76  tff(c_159, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_155])).
% 3.61/1.76  tff(c_42, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.61/1.76  tff(c_110, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_62, c_42])).
% 3.61/1.76  tff(c_160, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_110])).
% 3.61/1.76  tff(c_529, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_104])).
% 3.61/1.76  tff(c_105, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.61/1.76  tff(c_109, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_105])).
% 3.61/1.76  tff(c_40, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.61/1.76  tff(c_115, plain, (![A_37]: (k4_relat_1(A_37)=k2_funct_1(A_37) | ~v2_funct_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.61/1.76  tff(c_118, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_115])).
% 3.61/1.76  tff(c_121, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_48, c_118])).
% 3.61/1.76  tff(c_144, plain, (![A_38, B_39, C_40]: (k3_relset_1(A_38, B_39, C_40)=k4_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.61/1.76  tff(c_147, plain, (k3_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_144])).
% 3.61/1.76  tff(c_149, plain, (k3_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_147])).
% 3.61/1.76  tff(c_528, plain, (k3_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_149])).
% 3.61/1.76  tff(c_587, plain, (![A_74, B_75, C_76]: (m1_subset_1(k3_relset_1(A_74, B_75, C_76), k1_zfmisc_1(k2_zfmisc_1(B_75, A_74))) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.61/1.76  tff(c_606, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_528, c_587])).
% 3.61/1.76  tff(c_613, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_529, c_606])).
% 3.61/1.76  tff(c_10, plain, (![C_5, A_3, B_4]: (v1_relat_1(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.61/1.76  tff(c_631, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_613, c_10])).
% 3.61/1.76  tff(c_4, plain, (![A_1]: (k2_relat_1(k4_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.61/1.76  tff(c_128, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_121, c_4])).
% 3.61/1.76  tff(c_134, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_128])).
% 3.61/1.76  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.61/1.76  tff(c_6, plain, (![A_1]: (k1_relat_1(k4_relat_1(A_1))=k2_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.61/1.76  tff(c_18, plain, (![A_15, B_16, C_17]: (k3_relset_1(A_15, B_16, C_17)=k4_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.61/1.76  tff(c_630, plain, (k3_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k4_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_613, c_18])).
% 3.61/1.76  tff(c_12, plain, (![A_6, B_7, C_8]: (m1_subset_1(k3_relset_1(A_6, B_7, C_8), k1_zfmisc_1(k2_zfmisc_1(B_7, A_6))) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.61/1.76  tff(c_643, plain, (m1_subset_1(k4_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_630, c_12])).
% 3.61/1.76  tff(c_647, plain, (m1_subset_1(k4_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_613, c_643])).
% 3.61/1.76  tff(c_14, plain, (![A_9, B_10, C_11]: (k1_relset_1(A_9, B_10, C_11)=k1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.61/1.76  tff(c_661, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k4_relat_1(k2_funct_1('#skF_3')))=k1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_647, c_14])).
% 3.61/1.76  tff(c_801, plain, (![B_87, C_88, A_89]: (k1_xboole_0=B_87 | v1_funct_2(C_88, A_89, B_87) | k1_relset_1(A_89, B_87, C_88)!=A_89 | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_87))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.61/1.76  tff(c_810, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_funct_2(k4_relat_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k4_relat_1(k2_funct_1('#skF_3')))!=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_647, c_801])).
% 3.61/1.76  tff(c_824, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_funct_2(k4_relat_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | k1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_661, c_810])).
% 3.61/1.76  tff(c_842, plain, (k1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_824])).
% 3.61/1.76  tff(c_845, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_842])).
% 3.61/1.76  tff(c_847, plain, (k2_struct_0('#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_631, c_134, c_845])).
% 3.61/1.76  tff(c_46, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.61/1.76  tff(c_72, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_62, c_46])).
% 3.61/1.76  tff(c_531, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_72])).
% 3.61/1.76  tff(c_560, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_529, c_14])).
% 3.61/1.76  tff(c_876, plain, (![B_90, A_91, C_92]: (k1_xboole_0=B_90 | k1_relset_1(A_91, B_90, C_92)=A_91 | ~v1_funct_2(C_92, A_91, B_90) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.61/1.76  tff(c_897, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_529, c_876])).
% 3.61/1.76  tff(c_911, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_531, c_560, c_897])).
% 3.61/1.76  tff(c_912, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_847, c_911])).
% 3.61/1.76  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.61/1.76  tff(c_82, plain, (![A_32]: (~v1_xboole_0(u1_struct_0(A_32)) | ~l1_struct_0(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.61/1.76  tff(c_88, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_62, c_82])).
% 3.61/1.76  tff(c_92, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_88])).
% 3.61/1.76  tff(c_93, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_92])).
% 3.61/1.76  tff(c_530, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_93])).
% 3.61/1.76  tff(c_939, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_912, c_530])).
% 3.61/1.76  tff(c_944, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_939])).
% 3.61/1.76  tff(c_946, plain, (k1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_824])).
% 3.61/1.76  tff(c_951, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_946, c_6])).
% 3.61/1.76  tff(c_958, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_631, c_134, c_951])).
% 3.61/1.76  tff(c_984, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_958, c_531])).
% 3.61/1.76  tff(c_527, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_159])).
% 3.61/1.76  tff(c_982, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_958, c_527])).
% 3.61/1.76  tff(c_983, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_958, c_529])).
% 3.61/1.76  tff(c_1075, plain, (![A_96, B_97, C_98]: (k2_tops_2(A_96, B_97, C_98)=k2_funct_1(C_98) | ~v2_funct_1(C_98) | k2_relset_1(A_96, B_97, C_98)!=B_97 | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_2(C_98, A_96, B_97) | ~v1_funct_1(C_98))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.61/1.76  tff(c_1078, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_983, c_1075])).
% 3.61/1.76  tff(c_1084, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_984, c_982, c_40, c_1078])).
% 3.61/1.76  tff(c_171, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_72])).
% 3.61/1.76  tff(c_169, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_104])).
% 3.61/1.76  tff(c_204, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_169, c_14])).
% 3.61/1.76  tff(c_348, plain, (![B_63, A_64, C_65]: (k1_xboole_0=B_63 | k1_relset_1(A_64, B_63, C_65)=A_64 | ~v1_funct_2(C_65, A_64, B_63) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.61/1.76  tff(c_360, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_169, c_348])).
% 3.61/1.76  tff(c_367, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_204, c_360])).
% 3.61/1.76  tff(c_368, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_367])).
% 3.61/1.76  tff(c_380, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_171])).
% 3.61/1.76  tff(c_167, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_159])).
% 3.61/1.76  tff(c_377, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_368, c_167])).
% 3.61/1.76  tff(c_378, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_169])).
% 3.61/1.76  tff(c_447, plain, (![A_66, B_67, C_68]: (k2_tops_2(A_66, B_67, C_68)=k2_funct_1(C_68) | ~v2_funct_1(C_68) | k2_relset_1(A_66, B_67, C_68)!=B_67 | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~v1_funct_2(C_68, A_66, B_67) | ~v1_funct_1(C_68))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.61/1.76  tff(c_450, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_378, c_447])).
% 3.61/1.76  tff(c_456, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_380, c_377, c_40, c_450])).
% 3.61/1.76  tff(c_38, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.61/1.76  tff(c_165, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_63, c_62, c_62, c_63, c_63, c_62, c_62, c_38])).
% 3.61/1.76  tff(c_166, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_165])).
% 3.61/1.76  tff(c_218, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_160, c_160, c_166])).
% 3.61/1.76  tff(c_375, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_368, c_368, c_218])).
% 3.61/1.76  tff(c_498, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_456, c_375])).
% 3.61/1.76  tff(c_125, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_121, c_6])).
% 3.61/1.76  tff(c_132, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_125])).
% 3.61/1.76  tff(c_168, plain, (k3_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_149])).
% 3.61/1.76  tff(c_223, plain, (![A_54, B_55, C_56]: (m1_subset_1(k3_relset_1(A_54, B_55, C_56), k1_zfmisc_1(k2_zfmisc_1(B_55, A_54))) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.61/1.76  tff(c_250, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_168, c_223])).
% 3.61/1.76  tff(c_259, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_250])).
% 3.61/1.76  tff(c_374, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_259])).
% 3.61/1.76  tff(c_477, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_374, c_14])).
% 3.61/1.76  tff(c_492, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_477])).
% 3.61/1.76  tff(c_503, plain, $false, inference(negUnitSimplification, [status(thm)], [c_498, c_492])).
% 3.61/1.76  tff(c_504, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_367])).
% 3.61/1.76  tff(c_170, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_93])).
% 3.61/1.76  tff(c_519, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_504, c_170])).
% 3.61/1.76  tff(c_524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_519])).
% 3.61/1.76  tff(c_525, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_165])).
% 3.61/1.76  tff(c_581, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_160, c_525])).
% 3.61/1.76  tff(c_979, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_958, c_958, c_958, c_581])).
% 3.61/1.76  tff(c_1139, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1084, c_979])).
% 3.61/1.76  tff(c_16, plain, (![A_12, B_13, C_14]: (k2_relset_1(A_12, B_13, C_14)=k2_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.61/1.76  tff(c_619, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_613, c_16])).
% 3.61/1.76  tff(c_629, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_619])).
% 3.61/1.76  tff(c_975, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_958, c_629])).
% 3.61/1.76  tff(c_1140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1139, c_975])).
% 3.61/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.76  
% 3.61/1.76  Inference rules
% 3.61/1.76  ----------------------
% 3.61/1.76  #Ref     : 0
% 3.61/1.76  #Sup     : 257
% 3.61/1.76  #Fact    : 0
% 3.61/1.76  #Define  : 0
% 3.61/1.76  #Split   : 5
% 3.61/1.76  #Chain   : 0
% 3.61/1.76  #Close   : 0
% 3.61/1.76  
% 3.61/1.76  Ordering : KBO
% 3.61/1.76  
% 3.61/1.76  Simplification rules
% 3.61/1.76  ----------------------
% 3.61/1.76  #Subsume      : 4
% 3.61/1.76  #Demod        : 260
% 3.61/1.76  #Tautology    : 145
% 3.61/1.76  #SimpNegUnit  : 7
% 3.61/1.76  #BackRed      : 101
% 3.61/1.76  
% 3.61/1.76  #Partial instantiations: 0
% 3.61/1.76  #Strategies tried      : 1
% 3.61/1.76  
% 3.61/1.76  Timing (in seconds)
% 3.61/1.76  ----------------------
% 3.61/1.77  Preprocessing        : 0.36
% 3.61/1.77  Parsing              : 0.19
% 3.61/1.77  CNF conversion       : 0.02
% 3.61/1.77  Main loop            : 0.57
% 3.61/1.77  Inferencing          : 0.18
% 3.61/1.77  Reduction            : 0.20
% 3.61/1.77  Demodulation         : 0.14
% 3.61/1.77  BG Simplification    : 0.03
% 3.61/1.77  Subsumption          : 0.10
% 3.61/1.77  Abstraction          : 0.03
% 3.61/1.77  MUC search           : 0.00
% 3.61/1.77  Cooper               : 0.00
% 3.61/1.77  Total                : 1.00
% 3.61/1.77  Index Insertion      : 0.00
% 3.61/1.77  Index Deletion       : 0.00
% 3.61/1.77  Index Matching       : 0.00
% 3.61/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
