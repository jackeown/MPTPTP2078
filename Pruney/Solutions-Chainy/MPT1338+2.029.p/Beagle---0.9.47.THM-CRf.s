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
% DateTime   : Thu Dec  3 10:23:18 EST 2020

% Result     : Theorem 4.33s
% Output     : CNFRefutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :  210 (3227 expanded)
%              Number of leaves         :   53 (1156 expanded)
%              Depth                    :   17
%              Number of atoms          :  353 (9877 expanded)
%              Number of equality atoms :  111 (3154 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_173,negated_conjecture,(
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

tff(f_129,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_125,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_98,axiom,(
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

tff(f_137,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_149,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(c_70,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_71,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_79,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_71])).

tff(c_66,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_78,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_71])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_123,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_78,c_60])).

tff(c_20,plain,(
    ! [C_12,A_10,B_11] :
      ( v1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_127,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_123,c_20])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_16,plain,(
    ! [A_7] :
      ( v1_relat_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1420,plain,(
    ! [A_146] :
      ( k4_relat_1(A_146) = k2_funct_1(A_146)
      | ~ v2_funct_1(A_146)
      | ~ v1_funct_1(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1423,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1420])).

tff(c_1426,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_64,c_1423])).

tff(c_10,plain,(
    ! [A_5] :
      ( k1_relat_1(k4_relat_1(A_5)) = k2_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1433,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1426,c_10])).

tff(c_1439,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_1433])).

tff(c_2143,plain,(
    ! [A_191] :
      ( m1_subset_1(A_191,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_191),k2_relat_1(A_191))))
      | ~ v1_funct_1(A_191)
      | ~ v1_relat_1(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_24,plain,(
    ! [C_15,A_13,B_14] :
      ( v4_relat_1(C_15,A_13)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2198,plain,(
    ! [A_193] :
      ( v4_relat_1(A_193,k1_relat_1(A_193))
      | ~ v1_funct_1(A_193)
      | ~ v1_relat_1(A_193) ) ),
    inference(resolution,[status(thm)],[c_2143,c_24])).

tff(c_2210,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1439,c_2198])).

tff(c_2288,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2210])).

tff(c_2291,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_2288])).

tff(c_2295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_64,c_2291])).

tff(c_2297,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2210])).

tff(c_14,plain,(
    ! [A_7] :
      ( v1_funct_1(k2_funct_1(A_7))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2296,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2210])).

tff(c_2303,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2296])).

tff(c_2306,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_2303])).

tff(c_2310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_64,c_2306])).

tff(c_2312,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2296])).

tff(c_8,plain,(
    ! [A_5] :
      ( k2_relat_1(k4_relat_1(A_5)) = k1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1430,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1426,c_8])).

tff(c_1437,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_1430])).

tff(c_26,plain,(
    ! [A_16,B_17,C_18] :
      ( k2_relset_1(A_16,B_17,C_18) = k2_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2358,plain,(
    ! [A_203] :
      ( k2_relset_1(k1_relat_1(A_203),k2_relat_1(A_203),A_203) = k2_relat_1(A_203)
      | ~ v1_funct_1(A_203)
      | ~ v1_relat_1(A_203) ) ),
    inference(resolution,[status(thm)],[c_2143,c_26])).

tff(c_2373,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1439,c_2358])).

tff(c_2395,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2297,c_2312,c_1437,c_1437,c_2373])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_143,plain,(
    ! [C_54,A_55,B_56] :
      ( v4_relat_1(C_54,A_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_147,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_123,c_143])).

tff(c_1478,plain,(
    ! [B_149,A_150] :
      ( k1_relat_1(B_149) = A_150
      | ~ v1_partfun1(B_149,A_150)
      | ~ v4_relat_1(B_149,A_150)
      | ~ v1_relat_1(B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1481,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_147,c_1478])).

tff(c_1484,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_1481])).

tff(c_1485,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1484])).

tff(c_1526,plain,(
    ! [A_153,B_154,C_155] :
      ( k2_relset_1(A_153,B_154,C_155) = k2_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1534,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_123,c_1526])).

tff(c_58,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_128,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_78,c_58])).

tff(c_1555,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1534,c_128])).

tff(c_62,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_88,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_78,c_62])).

tff(c_1565,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1555,c_88])).

tff(c_1563,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1555,c_123])).

tff(c_1999,plain,(
    ! [B_185,C_186,A_187] :
      ( k1_xboole_0 = B_185
      | v1_partfun1(C_186,A_187)
      | ~ v1_funct_2(C_186,A_187,B_185)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_187,B_185)))
      | ~ v1_funct_1(C_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2005,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1563,c_1999])).

tff(c_2014,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1565,c_2005])).

tff(c_2015,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1485,c_2014])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_108,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0(u1_struct_0(A_45))
      | ~ l1_struct_0(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_114,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_108])).

tff(c_118,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_114])).

tff(c_119,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_118])).

tff(c_1564,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1555,c_119])).

tff(c_2037,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2015,c_1564])).

tff(c_2043,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2037])).

tff(c_2044,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1484])).

tff(c_2051,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2044,c_123])).

tff(c_2121,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2051,c_26])).

tff(c_2050,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2044,c_128])).

tff(c_2128,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2121,c_2050])).

tff(c_2053,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2044,c_88])).

tff(c_2135,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_2053])).

tff(c_2133,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_2121])).

tff(c_2134,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_2051])).

tff(c_2753,plain,(
    ! [A_228,B_229,C_230] :
      ( k2_tops_2(A_228,B_229,C_230) = k2_funct_1(C_230)
      | ~ v2_funct_1(C_230)
      | k2_relset_1(A_228,B_229,C_230) != B_229
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229)))
      | ~ v1_funct_2(C_230,A_228,B_229)
      | ~ v1_funct_1(C_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2759,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2134,c_2753])).

tff(c_2768,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2135,c_2133,c_56,c_2759])).

tff(c_229,plain,(
    ! [B_63,A_64] :
      ( k1_relat_1(B_63) = A_64
      | ~ v1_partfun1(B_63,A_64)
      | ~ v4_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_232,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_147,c_229])).

tff(c_235,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_232])).

tff(c_236,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_237,plain,(
    ! [A_65,B_66,C_67] :
      ( k2_relset_1(A_65,B_66,C_67) = k2_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_241,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_123,c_237])).

tff(c_242,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_128])).

tff(c_252,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_88])).

tff(c_250,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_123])).

tff(c_634,plain,(
    ! [B_96,C_97,A_98] :
      ( k1_xboole_0 = B_96
      | v1_partfun1(C_97,A_98)
      | ~ v1_funct_2(C_97,A_98,B_96)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_96)))
      | ~ v1_funct_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_637,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_250,c_634])).

tff(c_643,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_252,c_637])).

tff(c_644,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_643])).

tff(c_251,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_119])).

tff(c_662,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_251])).

tff(c_668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_662])).

tff(c_669,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k7_relat_1(B_4,A_3) = B_4
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_155,plain,
    ( k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_147,c_6])).

tff(c_158,plain,(
    k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_155])).

tff(c_672,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_158])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( k2_relat_1(k7_relat_1(B_2,A_1)) = k9_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_716,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_4])).

tff(c_720,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_716])).

tff(c_18,plain,(
    ! [B_9,A_8] :
      ( k10_relat_1(k2_funct_1(B_9),A_8) = k9_relat_1(B_9,A_8)
      | ~ v2_funct_1(B_9)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_174,plain,(
    ! [A_60] :
      ( k4_relat_1(A_60) = k2_funct_1(A_60)
      | ~ v2_funct_1(A_60)
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_177,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_174])).

tff(c_180,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_64,c_177])).

tff(c_187,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_10])).

tff(c_193,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_187])).

tff(c_767,plain,(
    ! [A_102] :
      ( m1_subset_1(A_102,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_102),k2_relat_1(A_102))))
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_822,plain,(
    ! [A_104] :
      ( v4_relat_1(A_104,k1_relat_1(A_104))
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(resolution,[status(thm)],[c_767,c_24])).

tff(c_834,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_822])).

tff(c_912,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_834])).

tff(c_915,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_912])).

tff(c_919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_64,c_915])).

tff(c_921,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_834])).

tff(c_920,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_834])).

tff(c_928,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_920])).

tff(c_938,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_928])).

tff(c_942,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_64,c_938])).

tff(c_944,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_920])).

tff(c_184,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_8])).

tff(c_191,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_184])).

tff(c_42,plain,(
    ! [A_31] :
      ( m1_subset_1(A_31,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_31),k2_relat_1(A_31))))
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1018,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( k8_relset_1(A_114,B_115,C_116,D_117) = k10_relat_1(C_116,D_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1140,plain,(
    ! [A_126,D_127] :
      ( k8_relset_1(k1_relat_1(A_126),k2_relat_1(A_126),A_126,D_127) = k10_relat_1(A_126,D_127)
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(resolution,[status(thm)],[c_42,c_1018])).

tff(c_1156,plain,(
    ! [D_127] :
      ( k8_relset_1(k2_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3'),D_127) = k10_relat_1(k2_funct_1('#skF_3'),D_127)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_1140])).

tff(c_1178,plain,(
    ! [D_127] : k8_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3'),D_127) = k10_relat_1(k2_funct_1('#skF_3'),D_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_944,c_191,c_1156])).

tff(c_785,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_767])).

tff(c_800,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_785])).

tff(c_1234,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_944,c_800])).

tff(c_30,plain,(
    ! [A_23,B_24,C_25] :
      ( k8_relset_1(A_23,B_24,C_25,B_24) = k1_relset_1(A_23,B_24,C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1236,plain,(
    k8_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3'),k1_relat_1('#skF_3')) = k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1234,c_30])).

tff(c_1254,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k10_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_1236])).

tff(c_675,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_123])).

tff(c_741,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_675,c_26])).

tff(c_674,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_128])).

tff(c_752,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_674])).

tff(c_677,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_88])).

tff(c_759,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_677])).

tff(c_757,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_741])).

tff(c_758,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_675])).

tff(c_1385,plain,(
    ! [A_143,B_144,C_145] :
      ( k2_tops_2(A_143,B_144,C_145) = k2_funct_1(C_145)
      | ~ v2_funct_1(C_145)
      | k2_relset_1(A_143,B_144,C_145) != B_144
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144)))
      | ~ v1_funct_2(C_145,A_143,B_144)
      | ~ v1_funct_1(C_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1391,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_758,c_1385])).

tff(c_1400,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_759,c_757,c_56,c_1391])).

tff(c_54,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_168,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_79,c_78,c_78,c_79,c_79,c_78,c_78,c_54])).

tff(c_169,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_821,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_752,c_752,c_669,c_669,c_169])).

tff(c_1402,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1400,c_821])).

tff(c_1403,plain,(
    k10_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1254,c_1402])).

tff(c_1410,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1403])).

tff(c_1413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_64,c_56,c_720,c_1410])).

tff(c_1414,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_2197,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_2128,c_2044,c_2044,c_2044,c_1414])).

tff(c_2771,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2768,c_2197])).

tff(c_2774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2395,c_2771])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.33/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.33/1.80  
% 4.33/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.33/1.80  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.33/1.80  
% 4.33/1.80  %Foreground sorts:
% 4.33/1.80  
% 4.33/1.80  
% 4.33/1.80  %Background operators:
% 4.33/1.80  
% 4.33/1.80  
% 4.33/1.80  %Foreground operators:
% 4.33/1.80  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.33/1.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.33/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.33/1.80  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.33/1.80  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.33/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.33/1.80  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.33/1.80  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.33/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.33/1.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.33/1.80  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.33/1.80  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.33/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.33/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.33/1.80  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.33/1.80  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.33/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.33/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.33/1.80  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.33/1.80  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.33/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.33/1.80  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.33/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.33/1.80  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.33/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.33/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.33/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.33/1.80  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.33/1.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.33/1.80  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.33/1.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.33/1.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.33/1.80  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.33/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.33/1.80  
% 4.70/1.83  tff(f_173, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 4.70/1.83  tff(f_129, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.70/1.83  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.70/1.83  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.70/1.83  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 4.70/1.83  tff(f_42, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 4.70/1.83  tff(f_125, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.70/1.83  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.70/1.83  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.70/1.83  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.70/1.83  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.70/1.83  tff(f_115, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 4.70/1.83  tff(f_137, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.70/1.83  tff(f_149, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 4.70/1.83  tff(f_36, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.70/1.83  tff(f_30, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.70/1.83  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 4.70/1.83  tff(f_84, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.70/1.83  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 4.70/1.83  tff(c_70, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.70/1.83  tff(c_71, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.70/1.83  tff(c_79, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_70, c_71])).
% 4.70/1.83  tff(c_66, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.70/1.83  tff(c_78, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_71])).
% 4.70/1.83  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.70/1.83  tff(c_123, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_78, c_60])).
% 4.70/1.83  tff(c_20, plain, (![C_12, A_10, B_11]: (v1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.70/1.83  tff(c_127, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_123, c_20])).
% 4.70/1.83  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.70/1.83  tff(c_16, plain, (![A_7]: (v1_relat_1(k2_funct_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.70/1.83  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.70/1.83  tff(c_1420, plain, (![A_146]: (k4_relat_1(A_146)=k2_funct_1(A_146) | ~v2_funct_1(A_146) | ~v1_funct_1(A_146) | ~v1_relat_1(A_146))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.70/1.83  tff(c_1423, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1420])).
% 4.70/1.83  tff(c_1426, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_64, c_1423])).
% 4.70/1.83  tff(c_10, plain, (![A_5]: (k1_relat_1(k4_relat_1(A_5))=k2_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.70/1.83  tff(c_1433, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1426, c_10])).
% 4.70/1.83  tff(c_1439, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_1433])).
% 4.70/1.83  tff(c_2143, plain, (![A_191]: (m1_subset_1(A_191, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_191), k2_relat_1(A_191)))) | ~v1_funct_1(A_191) | ~v1_relat_1(A_191))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.70/1.83  tff(c_24, plain, (![C_15, A_13, B_14]: (v4_relat_1(C_15, A_13) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.70/1.83  tff(c_2198, plain, (![A_193]: (v4_relat_1(A_193, k1_relat_1(A_193)) | ~v1_funct_1(A_193) | ~v1_relat_1(A_193))), inference(resolution, [status(thm)], [c_2143, c_24])).
% 4.70/1.83  tff(c_2210, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1439, c_2198])).
% 4.70/1.83  tff(c_2288, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2210])).
% 4.70/1.83  tff(c_2291, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_2288])).
% 4.70/1.83  tff(c_2295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_64, c_2291])).
% 4.70/1.83  tff(c_2297, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2210])).
% 4.70/1.83  tff(c_14, plain, (![A_7]: (v1_funct_1(k2_funct_1(A_7)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.70/1.83  tff(c_2296, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2210])).
% 4.70/1.83  tff(c_2303, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2296])).
% 4.70/1.83  tff(c_2306, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_2303])).
% 4.70/1.83  tff(c_2310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_64, c_2306])).
% 4.70/1.83  tff(c_2312, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2296])).
% 4.70/1.83  tff(c_8, plain, (![A_5]: (k2_relat_1(k4_relat_1(A_5))=k1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.70/1.83  tff(c_1430, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1426, c_8])).
% 4.70/1.83  tff(c_1437, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_1430])).
% 4.70/1.83  tff(c_26, plain, (![A_16, B_17, C_18]: (k2_relset_1(A_16, B_17, C_18)=k2_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.70/1.83  tff(c_2358, plain, (![A_203]: (k2_relset_1(k1_relat_1(A_203), k2_relat_1(A_203), A_203)=k2_relat_1(A_203) | ~v1_funct_1(A_203) | ~v1_relat_1(A_203))), inference(resolution, [status(thm)], [c_2143, c_26])).
% 4.70/1.83  tff(c_2373, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1439, c_2358])).
% 4.70/1.83  tff(c_2395, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2297, c_2312, c_1437, c_1437, c_2373])).
% 4.70/1.83  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.70/1.83  tff(c_143, plain, (![C_54, A_55, B_56]: (v4_relat_1(C_54, A_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.70/1.83  tff(c_147, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_123, c_143])).
% 4.70/1.83  tff(c_1478, plain, (![B_149, A_150]: (k1_relat_1(B_149)=A_150 | ~v1_partfun1(B_149, A_150) | ~v4_relat_1(B_149, A_150) | ~v1_relat_1(B_149))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.70/1.83  tff(c_1481, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_147, c_1478])).
% 4.70/1.83  tff(c_1484, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_1481])).
% 4.70/1.83  tff(c_1485, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1484])).
% 4.70/1.83  tff(c_1526, plain, (![A_153, B_154, C_155]: (k2_relset_1(A_153, B_154, C_155)=k2_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.70/1.83  tff(c_1534, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_123, c_1526])).
% 4.70/1.83  tff(c_58, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.70/1.83  tff(c_128, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_78, c_58])).
% 4.70/1.83  tff(c_1555, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1534, c_128])).
% 4.70/1.83  tff(c_62, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.70/1.83  tff(c_88, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_78, c_62])).
% 4.70/1.83  tff(c_1565, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1555, c_88])).
% 4.70/1.83  tff(c_1563, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1555, c_123])).
% 4.70/1.83  tff(c_1999, plain, (![B_185, C_186, A_187]: (k1_xboole_0=B_185 | v1_partfun1(C_186, A_187) | ~v1_funct_2(C_186, A_187, B_185) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_187, B_185))) | ~v1_funct_1(C_186))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.70/1.83  tff(c_2005, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1563, c_1999])).
% 4.70/1.83  tff(c_2014, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1565, c_2005])).
% 4.70/1.83  tff(c_2015, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1485, c_2014])).
% 4.70/1.83  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.70/1.83  tff(c_108, plain, (![A_45]: (~v1_xboole_0(u1_struct_0(A_45)) | ~l1_struct_0(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.70/1.83  tff(c_114, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_78, c_108])).
% 4.70/1.83  tff(c_118, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_114])).
% 4.70/1.83  tff(c_119, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_118])).
% 4.70/1.83  tff(c_1564, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1555, c_119])).
% 4.70/1.83  tff(c_2037, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2015, c_1564])).
% 4.70/1.83  tff(c_2043, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2037])).
% 4.70/1.83  tff(c_2044, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1484])).
% 4.70/1.83  tff(c_2051, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2044, c_123])).
% 4.70/1.83  tff(c_2121, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2051, c_26])).
% 4.70/1.83  tff(c_2050, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2044, c_128])).
% 4.70/1.83  tff(c_2128, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2121, c_2050])).
% 4.70/1.83  tff(c_2053, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2044, c_88])).
% 4.70/1.83  tff(c_2135, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_2053])).
% 4.70/1.83  tff(c_2133, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_2121])).
% 4.70/1.83  tff(c_2134, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_2051])).
% 4.70/1.83  tff(c_2753, plain, (![A_228, B_229, C_230]: (k2_tops_2(A_228, B_229, C_230)=k2_funct_1(C_230) | ~v2_funct_1(C_230) | k2_relset_1(A_228, B_229, C_230)!=B_229 | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))) | ~v1_funct_2(C_230, A_228, B_229) | ~v1_funct_1(C_230))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.70/1.83  tff(c_2759, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2134, c_2753])).
% 4.70/1.83  tff(c_2768, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2135, c_2133, c_56, c_2759])).
% 4.70/1.83  tff(c_229, plain, (![B_63, A_64]: (k1_relat_1(B_63)=A_64 | ~v1_partfun1(B_63, A_64) | ~v4_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.70/1.83  tff(c_232, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_147, c_229])).
% 4.70/1.83  tff(c_235, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_232])).
% 4.70/1.83  tff(c_236, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_235])).
% 4.70/1.83  tff(c_237, plain, (![A_65, B_66, C_67]: (k2_relset_1(A_65, B_66, C_67)=k2_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.70/1.83  tff(c_241, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_123, c_237])).
% 4.70/1.83  tff(c_242, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_128])).
% 4.70/1.83  tff(c_252, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_88])).
% 4.70/1.83  tff(c_250, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_123])).
% 4.70/1.83  tff(c_634, plain, (![B_96, C_97, A_98]: (k1_xboole_0=B_96 | v1_partfun1(C_97, A_98) | ~v1_funct_2(C_97, A_98, B_96) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_96))) | ~v1_funct_1(C_97))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.70/1.83  tff(c_637, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_250, c_634])).
% 4.70/1.83  tff(c_643, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_252, c_637])).
% 4.70/1.83  tff(c_644, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_236, c_643])).
% 4.70/1.83  tff(c_251, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_119])).
% 4.70/1.83  tff(c_662, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_644, c_251])).
% 4.70/1.83  tff(c_668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_662])).
% 4.70/1.83  tff(c_669, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_235])).
% 4.70/1.83  tff(c_6, plain, (![B_4, A_3]: (k7_relat_1(B_4, A_3)=B_4 | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.70/1.83  tff(c_155, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_147, c_6])).
% 4.70/1.83  tff(c_158, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_155])).
% 4.70/1.83  tff(c_672, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_669, c_158])).
% 4.70/1.83  tff(c_4, plain, (![B_2, A_1]: (k2_relat_1(k7_relat_1(B_2, A_1))=k9_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.70/1.83  tff(c_716, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_672, c_4])).
% 4.70/1.83  tff(c_720, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_716])).
% 4.70/1.83  tff(c_18, plain, (![B_9, A_8]: (k10_relat_1(k2_funct_1(B_9), A_8)=k9_relat_1(B_9, A_8) | ~v2_funct_1(B_9) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.70/1.83  tff(c_174, plain, (![A_60]: (k4_relat_1(A_60)=k2_funct_1(A_60) | ~v2_funct_1(A_60) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.70/1.83  tff(c_177, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_174])).
% 4.70/1.83  tff(c_180, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_64, c_177])).
% 4.70/1.83  tff(c_187, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_180, c_10])).
% 4.70/1.83  tff(c_193, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_187])).
% 4.70/1.83  tff(c_767, plain, (![A_102]: (m1_subset_1(A_102, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_102), k2_relat_1(A_102)))) | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.70/1.83  tff(c_822, plain, (![A_104]: (v4_relat_1(A_104, k1_relat_1(A_104)) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(resolution, [status(thm)], [c_767, c_24])).
% 4.70/1.83  tff(c_834, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_193, c_822])).
% 4.70/1.83  tff(c_912, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_834])).
% 4.70/1.83  tff(c_915, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_912])).
% 4.70/1.83  tff(c_919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_64, c_915])).
% 4.70/1.83  tff(c_921, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_834])).
% 4.70/1.83  tff(c_920, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_834])).
% 4.70/1.83  tff(c_928, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_920])).
% 4.70/1.83  tff(c_938, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_928])).
% 4.70/1.83  tff(c_942, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_64, c_938])).
% 4.70/1.83  tff(c_944, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_920])).
% 4.70/1.83  tff(c_184, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_180, c_8])).
% 4.70/1.83  tff(c_191, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_184])).
% 4.70/1.83  tff(c_42, plain, (![A_31]: (m1_subset_1(A_31, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_31), k2_relat_1(A_31)))) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.70/1.83  tff(c_1018, plain, (![A_114, B_115, C_116, D_117]: (k8_relset_1(A_114, B_115, C_116, D_117)=k10_relat_1(C_116, D_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.70/1.83  tff(c_1140, plain, (![A_126, D_127]: (k8_relset_1(k1_relat_1(A_126), k2_relat_1(A_126), A_126, D_127)=k10_relat_1(A_126, D_127) | ~v1_funct_1(A_126) | ~v1_relat_1(A_126))), inference(resolution, [status(thm)], [c_42, c_1018])).
% 4.70/1.83  tff(c_1156, plain, (![D_127]: (k8_relset_1(k2_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'), D_127)=k10_relat_1(k2_funct_1('#skF_3'), D_127) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_193, c_1140])).
% 4.70/1.83  tff(c_1178, plain, (![D_127]: (k8_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'), D_127)=k10_relat_1(k2_funct_1('#skF_3'), D_127))), inference(demodulation, [status(thm), theory('equality')], [c_921, c_944, c_191, c_1156])).
% 4.70/1.83  tff(c_785, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_191, c_767])).
% 4.70/1.83  tff(c_800, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_785])).
% 4.70/1.83  tff(c_1234, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_921, c_944, c_800])).
% 4.70/1.83  tff(c_30, plain, (![A_23, B_24, C_25]: (k8_relset_1(A_23, B_24, C_25, B_24)=k1_relset_1(A_23, B_24, C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.70/1.83  tff(c_1236, plain, (k8_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'), k1_relat_1('#skF_3'))=k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1234, c_30])).
% 4.70/1.83  tff(c_1254, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k10_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_1236])).
% 4.70/1.83  tff(c_675, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_669, c_123])).
% 4.70/1.83  tff(c_741, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_675, c_26])).
% 4.70/1.83  tff(c_674, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_669, c_128])).
% 4.70/1.83  tff(c_752, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_741, c_674])).
% 4.70/1.83  tff(c_677, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_669, c_88])).
% 4.70/1.83  tff(c_759, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_752, c_677])).
% 4.70/1.83  tff(c_757, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_752, c_741])).
% 4.70/1.83  tff(c_758, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_752, c_675])).
% 4.70/1.83  tff(c_1385, plain, (![A_143, B_144, C_145]: (k2_tops_2(A_143, B_144, C_145)=k2_funct_1(C_145) | ~v2_funct_1(C_145) | k2_relset_1(A_143, B_144, C_145)!=B_144 | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))) | ~v1_funct_2(C_145, A_143, B_144) | ~v1_funct_1(C_145))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.70/1.83  tff(c_1391, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_758, c_1385])).
% 4.70/1.83  tff(c_1400, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_759, c_757, c_56, c_1391])).
% 4.70/1.83  tff(c_54, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.70/1.83  tff(c_168, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_79, c_78, c_78, c_79, c_79, c_78, c_78, c_54])).
% 4.70/1.83  tff(c_169, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_168])).
% 4.70/1.83  tff(c_821, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_752, c_752, c_752, c_669, c_669, c_169])).
% 4.70/1.83  tff(c_1402, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1400, c_821])).
% 4.70/1.83  tff(c_1403, plain, (k10_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1254, c_1402])).
% 4.70/1.83  tff(c_1410, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_1403])).
% 4.70/1.83  tff(c_1413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_64, c_56, c_720, c_1410])).
% 4.70/1.83  tff(c_1414, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_168])).
% 4.70/1.83  tff(c_2197, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_2128, c_2044, c_2044, c_2044, c_1414])).
% 4.70/1.83  tff(c_2771, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2768, c_2197])).
% 4.70/1.83  tff(c_2774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2395, c_2771])).
% 4.70/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.70/1.83  
% 4.70/1.83  Inference rules
% 4.70/1.83  ----------------------
% 4.70/1.83  #Ref     : 0
% 4.70/1.83  #Sup     : 630
% 4.70/1.83  #Fact    : 0
% 4.70/1.83  #Define  : 0
% 4.70/1.83  #Split   : 18
% 4.70/1.83  #Chain   : 0
% 4.70/1.83  #Close   : 0
% 4.70/1.83  
% 4.70/1.83  Ordering : KBO
% 4.70/1.83  
% 4.70/1.83  Simplification rules
% 4.70/1.83  ----------------------
% 4.70/1.83  #Subsume      : 33
% 4.70/1.83  #Demod        : 819
% 4.70/1.83  #Tautology    : 350
% 4.70/1.83  #SimpNegUnit  : 7
% 4.70/1.83  #BackRed      : 94
% 4.70/1.83  
% 4.70/1.83  #Partial instantiations: 0
% 4.70/1.83  #Strategies tried      : 1
% 4.70/1.83  
% 4.70/1.83  Timing (in seconds)
% 4.70/1.83  ----------------------
% 4.70/1.83  Preprocessing        : 0.36
% 4.70/1.83  Parsing              : 0.19
% 4.70/1.83  CNF conversion       : 0.02
% 4.70/1.83  Main loop            : 0.68
% 4.70/1.83  Inferencing          : 0.24
% 4.70/1.83  Reduction            : 0.24
% 4.70/1.83  Demodulation         : 0.17
% 4.70/1.83  BG Simplification    : 0.03
% 4.70/1.83  Subsumption          : 0.09
% 4.70/1.83  Abstraction          : 0.03
% 4.70/1.83  MUC search           : 0.00
% 4.70/1.83  Cooper               : 0.00
% 4.70/1.83  Total                : 1.10
% 4.70/1.83  Index Insertion      : 0.00
% 4.70/1.83  Index Deletion       : 0.00
% 4.70/1.83  Index Matching       : 0.00
% 4.70/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
