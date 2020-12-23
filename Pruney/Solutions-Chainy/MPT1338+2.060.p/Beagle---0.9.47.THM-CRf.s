%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:22 EST 2020

% Result     : Theorem 34.07s
% Output     : CNFRefutation 34.41s
% Verified   : 
% Statistics : Number of formulae       :  331 (28176 expanded)
%              Number of leaves         :   53 (9797 expanded)
%              Depth                    :   24
%              Number of atoms          :  686 (84636 expanded)
%              Number of equality atoms :  187 (26312 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_220,negated_conjecture,(
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

tff(f_176,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_61,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_156,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_128,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_196,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_172,axiom,(
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

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_184,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_84,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_88,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_120,plain,(
    ! [A_71] :
      ( u1_struct_0(A_71) = k2_struct_0(A_71)
      | ~ l1_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_128,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_120])).

tff(c_127,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_120])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_178,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_127,c_78])).

tff(c_193619,plain,(
    ! [A_6172,B_6173,C_6174] :
      ( k2_relset_1(A_6172,B_6173,C_6174) = k2_relat_1(C_6174)
      | ~ m1_subset_1(C_6174,k1_zfmisc_1(k2_zfmisc_1(A_6172,B_6173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_193633,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_178,c_193619])).

tff(c_76,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_146,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_127,c_76])).

tff(c_193643,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193633,c_146])).

tff(c_173357,plain,(
    ! [C_4969,B_4970,A_4971] :
      ( v1_xboole_0(C_4969)
      | ~ m1_subset_1(C_4969,k1_zfmisc_1(k2_zfmisc_1(B_4970,A_4971)))
      | ~ v1_xboole_0(A_4971) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_173371,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_178,c_173357])).

tff(c_173382,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_173371])).

tff(c_193650,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193643,c_173382])).

tff(c_24,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [B_13,A_11] :
      ( v1_relat_1(B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_11))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_181,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_178,c_22])).

tff(c_190,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_181])).

tff(c_173185,plain,(
    ! [C_4937,A_4938,B_4939] :
      ( v4_relat_1(C_4937,A_4938)
      | ~ m1_subset_1(C_4937,k1_zfmisc_1(k2_zfmisc_1(A_4938,B_4939))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_173199,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_178,c_173185])).

tff(c_193511,plain,(
    ! [B_6159,A_6160] :
      ( k1_relat_1(B_6159) = A_6160
      | ~ v1_partfun1(B_6159,A_6160)
      | ~ v4_relat_1(B_6159,A_6160)
      | ~ v1_relat_1(B_6159) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_193523,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_173199,c_193511])).

tff(c_193533,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_193523])).

tff(c_193562,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_193533])).

tff(c_80,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_129,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_80])).

tff(c_139,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_129])).

tff(c_193658,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193643,c_139])).

tff(c_193657,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193643,c_178])).

tff(c_193809,plain,(
    ! [C_6180,A_6181,B_6182] :
      ( v1_partfun1(C_6180,A_6181)
      | ~ v1_funct_2(C_6180,A_6181,B_6182)
      | ~ v1_funct_1(C_6180)
      | ~ m1_subset_1(C_6180,k1_zfmisc_1(k2_zfmisc_1(A_6181,B_6182)))
      | v1_xboole_0(B_6182) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_193812,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_193657,c_193809])).

tff(c_193829,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_193658,c_193812])).

tff(c_193831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_193650,c_193562,c_193829])).

tff(c_193832,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_193533])).

tff(c_193843,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193832,c_178])).

tff(c_193993,plain,(
    ! [A_6189,B_6190,C_6191] :
      ( k2_relset_1(A_6189,B_6190,C_6191) = k2_relat_1(C_6191)
      | ~ m1_subset_1(C_6191,k1_zfmisc_1(k2_zfmisc_1(A_6189,B_6190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_194007,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_193843,c_193993])).

tff(c_193844,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193832,c_146])).

tff(c_194119,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194007,c_193844])).

tff(c_193845,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193832,c_139])).

tff(c_194130,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194119,c_193845])).

tff(c_194124,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194119,c_194007])).

tff(c_74,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_194126,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194119,c_193843])).

tff(c_195408,plain,(
    ! [A_6277,B_6278,C_6279] :
      ( k2_tops_2(A_6277,B_6278,C_6279) = k2_funct_1(C_6279)
      | ~ v2_funct_1(C_6279)
      | k2_relset_1(A_6277,B_6278,C_6279) != B_6278
      | ~ m1_subset_1(C_6279,k1_zfmisc_1(k2_zfmisc_1(A_6277,B_6278)))
      | ~ v1_funct_2(C_6279,A_6277,B_6278)
      | ~ v1_funct_1(C_6279) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_195424,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_194126,c_195408])).

tff(c_195446,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_194130,c_194124,c_74,c_195424])).

tff(c_34562,plain,(
    ! [A_2071,B_2072,C_2073] :
      ( k2_relset_1(A_2071,B_2072,C_2073) = k2_relat_1(C_2073)
      | ~ m1_subset_1(C_2073,k1_zfmisc_1(k2_zfmisc_1(A_2071,B_2072))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_34579,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_178,c_34562])).

tff(c_34617,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34579,c_146])).

tff(c_377,plain,(
    ! [C_121,B_122,A_123] :
      ( v1_xboole_0(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(B_122,A_123)))
      | ~ v1_xboole_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_391,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_178,c_377])).

tff(c_430,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_391])).

tff(c_34624,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34617,c_430])).

tff(c_278,plain,(
    ! [C_106,A_107,B_108] :
      ( v4_relat_1(C_106,A_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_292,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_178,c_278])).

tff(c_448,plain,(
    ! [B_129,A_130] :
      ( k1_relat_1(B_129) = A_130
      | ~ v1_partfun1(B_129,A_130)
      | ~ v4_relat_1(B_129,A_130)
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_460,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_292,c_448])).

tff(c_470,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_460])).

tff(c_34415,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_470])).

tff(c_34631,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34617,c_139])).

tff(c_34630,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34617,c_178])).

tff(c_35260,plain,(
    ! [C_2100,A_2101,B_2102] :
      ( v1_partfun1(C_2100,A_2101)
      | ~ v1_funct_2(C_2100,A_2101,B_2102)
      | ~ v1_funct_1(C_2100)
      | ~ m1_subset_1(C_2100,k1_zfmisc_1(k2_zfmisc_1(A_2101,B_2102)))
      | v1_xboole_0(B_2102) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_35272,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34630,c_35260])).

tff(c_35292,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_34631,c_35272])).

tff(c_35294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34624,c_34415,c_35292])).

tff(c_35295,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_470])).

tff(c_35306,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35295,c_178])).

tff(c_44,plain,(
    ! [A_40,B_41,C_42] :
      ( k2_relset_1(A_40,B_41,C_42) = k2_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_35397,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_35306,c_44])).

tff(c_35307,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35295,c_146])).

tff(c_35521,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35397,c_35307])).

tff(c_35308,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35295,c_139])).

tff(c_35538,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35521,c_35308])).

tff(c_35531,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35521,c_35397])).

tff(c_35536,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35521,c_35306])).

tff(c_53583,plain,(
    ! [A_2546,B_2547,C_2548] :
      ( k2_tops_2(A_2546,B_2547,C_2548) = k2_funct_1(C_2548)
      | ~ v2_funct_1(C_2548)
      | k2_relset_1(A_2546,B_2547,C_2548) != B_2547
      | ~ m1_subset_1(C_2548,k1_zfmisc_1(k2_zfmisc_1(A_2546,B_2547)))
      | ~ v1_funct_2(C_2548,A_2546,B_2547)
      | ~ v1_funct_1(C_2548) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_53598,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_35536,c_53583])).

tff(c_53615,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_35538,c_35531,c_74,c_53598])).

tff(c_72,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_217,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_128,c_127,c_127,c_128,c_128,c_127,c_127,c_72])).

tff(c_218,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_35303,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35295,c_35295,c_218])).

tff(c_35707,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35521,c_35521,c_35521,c_35303])).

tff(c_53618,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53615,c_35707])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_431,plain,(
    ! [C_126,A_127,B_128] :
      ( v1_xboole_0(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ v1_xboole_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_445,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_178,c_431])).

tff(c_447,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_445])).

tff(c_35298,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35295,c_447])).

tff(c_36334,plain,(
    ! [C_2147,A_2148,B_2149] :
      ( v1_funct_1(k2_funct_1(C_2147))
      | k2_relset_1(A_2148,B_2149,C_2147) != B_2149
      | ~ v2_funct_1(C_2147)
      | ~ m1_subset_1(C_2147,k1_zfmisc_1(k2_zfmisc_1(A_2148,B_2149)))
      | ~ v1_funct_2(C_2147,A_2148,B_2149)
      | ~ v1_funct_1(C_2147) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_36349,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_35536,c_36334])).

tff(c_36366,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_35538,c_74,c_35531,c_36349])).

tff(c_28,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,A_18) = B_19
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_296,plain,
    ( k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_292,c_28])).

tff(c_299,plain,(
    k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_296])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( k2_relat_1(k7_relat_1(B_17,A_16)) = k9_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_303,plain,
    ( k9_relat_1('#skF_3',k2_struct_0('#skF_1')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_26])).

tff(c_307,plain,(
    k9_relat_1('#skF_3',k2_struct_0('#skF_1')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_303])).

tff(c_35300,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35295,c_307])).

tff(c_35570,plain,(
    ! [A_2109,B_2110] :
      ( k9_relat_1(k2_funct_1(A_2109),k9_relat_1(A_2109,B_2110)) = B_2110
      | ~ r1_tarski(B_2110,k1_relat_1(A_2109))
      | ~ v2_funct_1(A_2109)
      | ~ v1_funct_1(A_2109)
      | ~ v1_relat_1(A_2109) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_35585,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_35300,c_35570])).

tff(c_35592,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_82,c_74,c_8,c_35585])).

tff(c_30,plain,(
    ! [A_20,B_22] :
      ( k9_relat_1(k2_funct_1(A_20),k9_relat_1(A_20,B_22)) = B_22
      | ~ r1_tarski(B_22,k1_relat_1(A_20))
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_35662,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35592,c_30])).

tff(c_36526,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36366,c_35662])).

tff(c_36527,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_36526])).

tff(c_36779,plain,(
    ! [C_2173,B_2174,A_2175] :
      ( m1_subset_1(k2_funct_1(C_2173),k1_zfmisc_1(k2_zfmisc_1(B_2174,A_2175)))
      | k2_relset_1(A_2175,B_2174,C_2173) != B_2174
      | ~ v2_funct_1(C_2173)
      | ~ m1_subset_1(C_2173,k1_zfmisc_1(k2_zfmisc_1(A_2175,B_2174)))
      | ~ v1_funct_2(C_2173,A_2175,B_2174)
      | ~ v1_funct_1(C_2173) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_36815,plain,(
    ! [C_2173,B_2174,A_2175] :
      ( v1_relat_1(k2_funct_1(C_2173))
      | ~ v1_relat_1(k2_zfmisc_1(B_2174,A_2175))
      | k2_relset_1(A_2175,B_2174,C_2173) != B_2174
      | ~ v2_funct_1(C_2173)
      | ~ m1_subset_1(C_2173,k1_zfmisc_1(k2_zfmisc_1(A_2175,B_2174)))
      | ~ v1_funct_2(C_2173,A_2175,B_2174)
      | ~ v1_funct_1(C_2173) ) ),
    inference(resolution,[status(thm)],[c_36779,c_22])).

tff(c_53441,plain,(
    ! [C_2541,A_2542,B_2543] :
      ( v1_relat_1(k2_funct_1(C_2541))
      | k2_relset_1(A_2542,B_2543,C_2541) != B_2543
      | ~ v2_funct_1(C_2541)
      | ~ m1_subset_1(C_2541,k1_zfmisc_1(k2_zfmisc_1(A_2542,B_2543)))
      | ~ v1_funct_2(C_2541,A_2542,B_2543)
      | ~ v1_funct_1(C_2541) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_36815])).

tff(c_53499,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_35536,c_53441])).

tff(c_53519,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_35538,c_74,c_35531,c_53499])).

tff(c_53521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36527,c_53519])).

tff(c_53523,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_36526])).

tff(c_53868,plain,(
    ! [C_2554,B_2555,A_2556] :
      ( m1_subset_1(k2_funct_1(C_2554),k1_zfmisc_1(k2_zfmisc_1(B_2555,A_2556)))
      | k2_relset_1(A_2556,B_2555,C_2554) != B_2555
      | ~ v2_funct_1(C_2554)
      | ~ m1_subset_1(C_2554,k1_zfmisc_1(k2_zfmisc_1(A_2556,B_2555)))
      | ~ v1_funct_2(C_2554,A_2556,B_2555)
      | ~ v1_funct_1(C_2554) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_34,plain,(
    ! [C_25,A_23,B_24] :
      ( v4_relat_1(C_25,A_23)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_105842,plain,(
    ! [C_3609,B_3610,A_3611] :
      ( v4_relat_1(k2_funct_1(C_3609),B_3610)
      | k2_relset_1(A_3611,B_3610,C_3609) != B_3610
      | ~ v2_funct_1(C_3609)
      | ~ m1_subset_1(C_3609,k1_zfmisc_1(k2_zfmisc_1(A_3611,B_3610)))
      | ~ v1_funct_2(C_3609,A_3611,B_3610)
      | ~ v1_funct_1(C_3609) ) ),
    inference(resolution,[status(thm)],[c_53868,c_34])).

tff(c_105900,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_35536,c_105842])).

tff(c_105920,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_35538,c_74,c_35531,c_105900])).

tff(c_58,plain,(
    ! [B_52,A_51] :
      ( k1_relat_1(B_52) = A_51
      | ~ v1_partfun1(B_52,A_51)
      | ~ v4_relat_1(B_52,A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_105925,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_105920,c_58])).

tff(c_105931,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53523,c_105925])).

tff(c_106026,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_105931])).

tff(c_36462,plain,(
    ! [C_2161,B_2162,A_2163] :
      ( v1_funct_2(k2_funct_1(C_2161),B_2162,A_2163)
      | k2_relset_1(A_2163,B_2162,C_2161) != B_2162
      | ~ v2_funct_1(C_2161)
      | ~ m1_subset_1(C_2161,k1_zfmisc_1(k2_zfmisc_1(A_2163,B_2162)))
      | ~ v1_funct_2(C_2161,A_2163,B_2162)
      | ~ v1_funct_1(C_2161) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_36477,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_35536,c_36462])).

tff(c_36494,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_35538,c_74,c_35531,c_36477])).

tff(c_60,plain,(
    ! [C_55,B_54,A_53] :
      ( m1_subset_1(k2_funct_1(C_55),k1_zfmisc_1(k2_zfmisc_1(B_54,A_53)))
      | k2_relset_1(A_53,B_54,C_55) != B_54
      | ~ v2_funct_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_2(C_55,A_53,B_54)
      | ~ v1_funct_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_105928,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_105920,c_28])).

tff(c_105934,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53523,c_105928])).

tff(c_105945,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_105934,c_26])).

tff(c_105955,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53523,c_35592,c_105945])).

tff(c_118244,plain,(
    ! [B_3789,A_3790,C_3791] :
      ( k2_relset_1(B_3789,A_3790,k2_funct_1(C_3791)) = k2_relat_1(k2_funct_1(C_3791))
      | k2_relset_1(A_3790,B_3789,C_3791) != B_3789
      | ~ v2_funct_1(C_3791)
      | ~ m1_subset_1(C_3791,k1_zfmisc_1(k2_zfmisc_1(A_3790,B_3789)))
      | ~ v1_funct_2(C_3791,A_3790,B_3789)
      | ~ v1_funct_1(C_3791) ) ),
    inference(resolution,[status(thm)],[c_53868,c_44])).

tff(c_118314,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_35536,c_118244])).

tff(c_118334,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_35538,c_74,c_35531,c_105955,c_118314])).

tff(c_40,plain,(
    ! [A_34,B_35,C_36] :
      ( m1_subset_1(k2_relset_1(A_34,B_35,C_36),k1_zfmisc_1(B_35))
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_118346,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1(k1_relat_1('#skF_3')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_118334,c_40])).

tff(c_118356,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_118346])).

tff(c_118362,plain,
    ( k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_118356])).

tff(c_118369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_35538,c_35536,c_74,c_35531,c_118362])).

tff(c_118371,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_118346])).

tff(c_46,plain,(
    ! [C_46,A_43,B_44] :
      ( v1_partfun1(C_46,A_43)
      | ~ v1_funct_2(C_46,A_43,B_44)
      | ~ v1_funct_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | v1_xboole_0(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_118432,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_118371,c_46])).

tff(c_118509,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36366,c_36494,c_118432])).

tff(c_118511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35298,c_106026,c_118509])).

tff(c_118512,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_105931])).

tff(c_73065,plain,(
    ! [C_2983,B_2984,A_2985] :
      ( v4_relat_1(k2_funct_1(C_2983),B_2984)
      | k2_relset_1(A_2985,B_2984,C_2983) != B_2984
      | ~ v2_funct_1(C_2983)
      | ~ m1_subset_1(C_2983,k1_zfmisc_1(k2_zfmisc_1(A_2985,B_2984)))
      | ~ v1_funct_2(C_2983,A_2985,B_2984)
      | ~ v1_funct_1(C_2983) ) ),
    inference(resolution,[status(thm)],[c_53868,c_34])).

tff(c_73123,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_35536,c_73065])).

tff(c_73143,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_35538,c_74,c_35531,c_73123])).

tff(c_73148,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_73143,c_58])).

tff(c_73154,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53523,c_73148])).

tff(c_73312,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_73154])).

tff(c_73151,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_73143,c_28])).

tff(c_73157,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53523,c_73151])).

tff(c_73168,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_73157,c_26])).

tff(c_73178,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53523,c_35592,c_73168])).

tff(c_85140,plain,(
    ! [B_3159,A_3160,C_3161] :
      ( k2_relset_1(B_3159,A_3160,k2_funct_1(C_3161)) = k2_relat_1(k2_funct_1(C_3161))
      | k2_relset_1(A_3160,B_3159,C_3161) != B_3159
      | ~ v2_funct_1(C_3161)
      | ~ m1_subset_1(C_3161,k1_zfmisc_1(k2_zfmisc_1(A_3160,B_3159)))
      | ~ v1_funct_2(C_3161,A_3160,B_3159)
      | ~ v1_funct_1(C_3161) ) ),
    inference(resolution,[status(thm)],[c_53868,c_44])).

tff(c_85210,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_35536,c_85140])).

tff(c_85230,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_35538,c_74,c_35531,c_73178,c_85210])).

tff(c_85242,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1(k1_relat_1('#skF_3')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_85230,c_40])).

tff(c_85252,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_85242])).

tff(c_85258,plain,
    ( k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_85252])).

tff(c_85265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_35538,c_35536,c_74,c_35531,c_85258])).

tff(c_85267,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_85242])).

tff(c_85325,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_85267,c_46])).

tff(c_85399,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36366,c_36494,c_85325])).

tff(c_85401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35298,c_73312,c_85399])).

tff(c_85402,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_73154])).

tff(c_53522,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_36526])).

tff(c_53971,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_53522])).

tff(c_85404,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85402,c_53971])).

tff(c_85407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_85404])).

tff(c_85409,plain,(
    r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_53522])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_85418,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_85409,c_4])).

tff(c_85604,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_85418])).

tff(c_118514,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118512,c_85604])).

tff(c_118520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_118514])).

tff(c_118521,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_85418])).

tff(c_42,plain,(
    ! [A_37,B_38,C_39] :
      ( k1_relset_1(A_37,B_38,C_39) = k1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_171598,plain,(
    ! [B_4817,A_4818,C_4819] :
      ( k1_relset_1(B_4817,A_4818,k2_funct_1(C_4819)) = k1_relat_1(k2_funct_1(C_4819))
      | k2_relset_1(A_4818,B_4817,C_4819) != B_4817
      | ~ v2_funct_1(C_4819)
      | ~ m1_subset_1(C_4819,k1_zfmisc_1(k2_zfmisc_1(A_4818,B_4817)))
      | ~ v1_funct_2(C_4819,A_4818,B_4817)
      | ~ v1_funct_1(C_4819) ) ),
    inference(resolution,[status(thm)],[c_53868,c_42])).

tff(c_171668,plain,
    ( k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_35536,c_171598])).

tff(c_171688,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_35538,c_74,c_35531,c_118521,c_171668])).

tff(c_171690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53618,c_171688])).

tff(c_171691,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_445])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_171696,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_171691,c_2])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_171706,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171696,c_171696,c_14])).

tff(c_171692,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_445])).

tff(c_171738,plain,(
    ! [A_4822] :
      ( A_4822 = '#skF_3'
      | ~ v1_xboole_0(A_4822) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171696,c_2])).

tff(c_171745,plain,(
    k2_struct_0('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_171692,c_171738])).

tff(c_16,plain,(
    ! [B_8,A_6] :
      ( v1_xboole_0(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_191,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_178,c_16])).

tff(c_219,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_171753,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3',k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171745,c_219])).

tff(c_171929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_171691,c_171706,c_171753])).

tff(c_171931,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_68,plain,(
    ! [A_57] :
      ( ~ v1_xboole_0(k2_struct_0(A_57))
      | ~ l1_struct_0(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_171938,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_171931,c_68])).

tff(c_171944,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_171938])).

tff(c_171946,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_171944])).

tff(c_171947,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_171948,plain,(
    v1_xboole_0(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_171952,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_171947,c_2])).

tff(c_171957,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171952,c_2])).

tff(c_172001,plain,(
    k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_171948,c_171957])).

tff(c_172004,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172001,c_178])).

tff(c_171954,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171952,c_171952,c_14])).

tff(c_172834,plain,(
    ! [A_4910,B_4911,C_4912] :
      ( k2_relset_1(A_4910,B_4911,C_4912) = k2_relat_1(C_4912)
      | ~ m1_subset_1(C_4912,k1_zfmisc_1(k2_zfmisc_1(A_4910,B_4911))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_172973,plain,(
    ! [B_4928,C_4929] :
      ( k2_relset_1('#skF_3',B_4928,C_4929) = k2_relat_1(C_4929)
      | ~ m1_subset_1(C_4929,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171954,c_172834])).

tff(c_172979,plain,(
    ! [B_4928] : k2_relset_1('#skF_3',B_4928,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_172004,c_172973])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_172033,plain,(
    ! [B_4836,A_4837] :
      ( B_4836 = '#skF_3'
      | A_4837 = '#skF_3'
      | k2_zfmisc_1(A_4837,B_4836) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171952,c_171952,c_171952,c_10])).

tff(c_172043,plain,
    ( k2_struct_0('#skF_2') = '#skF_3'
    | k2_struct_0('#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_172001,c_172033])).

tff(c_172048,plain,(
    k2_struct_0('#skF_1') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_172043])).

tff(c_172051,plain,(
    k2_relset_1('#skF_3',k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172048,c_146])).

tff(c_172981,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172979,c_172051])).

tff(c_173003,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_172981,c_68])).

tff(c_173007,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_173003])).

tff(c_173008,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_173007])).

tff(c_173020,plain,(
    ! [A_4933,B_4934,C_4935] :
      ( m1_subset_1(k2_relset_1(A_4933,B_4934,C_4935),k1_zfmisc_1(B_4934))
      | ~ m1_subset_1(C_4935,k1_zfmisc_1(k2_zfmisc_1(A_4933,B_4934))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_173072,plain,(
    ! [B_4928] :
      ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1(B_4928))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_4928))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172979,c_173020])).

tff(c_173099,plain,(
    ! [B_4936] : m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1(B_4936)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172004,c_171954,c_173072])).

tff(c_172178,plain,(
    ! [C_4863,A_4864,B_4865] :
      ( v1_xboole_0(C_4863)
      | ~ m1_subset_1(C_4863,k1_zfmisc_1(k2_zfmisc_1(A_4864,B_4865)))
      | ~ v1_xboole_0(A_4864) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_172184,plain,(
    ! [C_4863] :
      ( v1_xboole_0(C_4863)
      | ~ m1_subset_1(C_4863,k1_zfmisc_1('#skF_3'))
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171954,c_172178])).

tff(c_172190,plain,(
    ! [C_4863] :
      ( v1_xboole_0(C_4863)
      | ~ m1_subset_1(C_4863,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171947,c_172184])).

tff(c_173121,plain,(
    v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_173099,c_172190])).

tff(c_173159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173008,c_173121])).

tff(c_173160,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_172043])).

tff(c_173171,plain,
    ( ~ v1_xboole_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_173160,c_68])).

tff(c_173175,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_171947,c_173171])).

tff(c_173177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_173175])).

tff(c_173178,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_193838,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193832,c_193832,c_193832,c_173178])).

tff(c_194361,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194119,c_194119,c_193838])).

tff(c_195450,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195446,c_194361])).

tff(c_195009,plain,(
    ! [C_6250,A_6251,B_6252] :
      ( v1_funct_1(k2_funct_1(C_6250))
      | k2_relset_1(A_6251,B_6252,C_6250) != B_6252
      | ~ v2_funct_1(C_6250)
      | ~ m1_subset_1(C_6250,k1_zfmisc_1(k2_zfmisc_1(A_6251,B_6252)))
      | ~ v1_funct_2(C_6250,A_6251,B_6252)
      | ~ v1_funct_1(C_6250) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_195021,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_194126,c_195009])).

tff(c_195041,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_194130,c_74,c_194124,c_195021])).

tff(c_173265,plain,(
    ! [B_4957,A_4958] :
      ( k7_relat_1(B_4957,A_4958) = B_4957
      | ~ v4_relat_1(B_4957,A_4958)
      | ~ v1_relat_1(B_4957) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_173277,plain,
    ( k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_173199,c_173265])).

tff(c_173287,plain,(
    k7_relat_1('#skF_3',k2_struct_0('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_173277])).

tff(c_193837,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193832,c_173287])).

tff(c_193883,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_193837,c_26])).

tff(c_193887,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_193883])).

tff(c_194307,plain,(
    ! [A_6202,B_6203] :
      ( k9_relat_1(k2_funct_1(A_6202),k9_relat_1(A_6202,B_6203)) = B_6203
      | ~ r1_tarski(B_6203,k1_relat_1(A_6202))
      | ~ v2_funct_1(A_6202)
      | ~ v1_funct_1(A_6202)
      | ~ v1_relat_1(A_6202) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_194322,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_193887,c_194307])).

tff(c_194329,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_82,c_74,c_8,c_194322])).

tff(c_194335,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_194329,c_30])).

tff(c_195460,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195041,c_194335])).

tff(c_195461,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_195460])).

tff(c_195826,plain,(
    ! [C_6291,B_6292,A_6293] :
      ( m1_subset_1(k2_funct_1(C_6291),k1_zfmisc_1(k2_zfmisc_1(B_6292,A_6293)))
      | k2_relset_1(A_6293,B_6292,C_6291) != B_6292
      | ~ v2_funct_1(C_6291)
      | ~ m1_subset_1(C_6291,k1_zfmisc_1(k2_zfmisc_1(A_6293,B_6292)))
      | ~ v1_funct_2(C_6291,A_6293,B_6292)
      | ~ v1_funct_1(C_6291) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_195862,plain,(
    ! [C_6291,B_6292,A_6293] :
      ( v1_relat_1(k2_funct_1(C_6291))
      | ~ v1_relat_1(k2_zfmisc_1(B_6292,A_6293))
      | k2_relset_1(A_6293,B_6292,C_6291) != B_6292
      | ~ v2_funct_1(C_6291)
      | ~ m1_subset_1(C_6291,k1_zfmisc_1(k2_zfmisc_1(A_6293,B_6292)))
      | ~ v1_funct_2(C_6291,A_6293,B_6292)
      | ~ v1_funct_1(C_6291) ) ),
    inference(resolution,[status(thm)],[c_195826,c_22])).

tff(c_211499,plain,(
    ! [C_6623,A_6624,B_6625] :
      ( v1_relat_1(k2_funct_1(C_6623))
      | k2_relset_1(A_6624,B_6625,C_6623) != B_6625
      | ~ v2_funct_1(C_6623)
      | ~ m1_subset_1(C_6623,k1_zfmisc_1(k2_zfmisc_1(A_6624,B_6625)))
      | ~ v1_funct_2(C_6623,A_6624,B_6625)
      | ~ v1_funct_1(C_6623) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_195862])).

tff(c_211554,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_194126,c_211499])).

tff(c_211577,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_194130,c_74,c_194124,c_211554])).

tff(c_211579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195461,c_211577])).

tff(c_211581,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_195460])).

tff(c_212105,plain,(
    ! [C_6643,B_6644,A_6645] :
      ( m1_subset_1(k2_funct_1(C_6643),k1_zfmisc_1(k2_zfmisc_1(B_6644,A_6645)))
      | k2_relset_1(A_6645,B_6644,C_6643) != B_6644
      | ~ v2_funct_1(C_6643)
      | ~ m1_subset_1(C_6643,k1_zfmisc_1(k2_zfmisc_1(A_6645,B_6644)))
      | ~ v1_funct_2(C_6643,A_6645,B_6644)
      | ~ v1_funct_1(C_6643) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_234603,plain,(
    ! [C_7095,B_7096,A_7097] :
      ( v4_relat_1(k2_funct_1(C_7095),B_7096)
      | k2_relset_1(A_7097,B_7096,C_7095) != B_7096
      | ~ v2_funct_1(C_7095)
      | ~ m1_subset_1(C_7095,k1_zfmisc_1(k2_zfmisc_1(A_7097,B_7096)))
      | ~ v1_funct_2(C_7095,A_7097,B_7096)
      | ~ v1_funct_1(C_7095) ) ),
    inference(resolution,[status(thm)],[c_212105,c_34])).

tff(c_234658,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_194126,c_234603])).

tff(c_234681,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_194130,c_74,c_194124,c_234658])).

tff(c_234689,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_234681,c_28])).

tff(c_234695,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211581,c_234689])).

tff(c_234706,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_234695,c_26])).

tff(c_234716,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211581,c_194329,c_234706])).

tff(c_244727,plain,(
    ! [B_7234,A_7235,C_7236] :
      ( k2_relset_1(B_7234,A_7235,k2_funct_1(C_7236)) = k2_relat_1(k2_funct_1(C_7236))
      | k2_relset_1(A_7235,B_7234,C_7236) != B_7234
      | ~ v2_funct_1(C_7236)
      | ~ m1_subset_1(C_7236,k1_zfmisc_1(k2_zfmisc_1(A_7235,B_7234)))
      | ~ v1_funct_2(C_7236,A_7235,B_7234)
      | ~ v1_funct_1(C_7236) ) ),
    inference(resolution,[status(thm)],[c_212105,c_44])).

tff(c_244794,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_194126,c_244727])).

tff(c_244817,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_194130,c_74,c_194124,c_234716,c_244794])).

tff(c_244819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195450,c_244817])).

tff(c_244821,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_173371])).

tff(c_244847,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_244821,c_68])).

tff(c_244850,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_244847])).

tff(c_244852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_244850])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:30:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 34.07/24.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.07/24.75  
% 34.07/24.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.07/24.76  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 34.07/24.76  
% 34.07/24.76  %Foreground sorts:
% 34.07/24.76  
% 34.07/24.76  
% 34.07/24.76  %Background operators:
% 34.07/24.76  
% 34.07/24.76  
% 34.07/24.76  %Foreground operators:
% 34.07/24.76  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 34.07/24.76  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 34.07/24.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 34.07/24.76  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 34.07/24.76  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 34.07/24.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.07/24.76  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 34.07/24.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 34.07/24.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 34.07/24.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 34.07/24.76  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 34.07/24.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 34.07/24.76  tff('#skF_2', type, '#skF_2': $i).
% 34.07/24.76  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 34.07/24.76  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 34.07/24.76  tff('#skF_3', type, '#skF_3': $i).
% 34.07/24.76  tff('#skF_1', type, '#skF_1': $i).
% 34.07/24.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 34.07/24.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 34.07/24.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 34.07/24.76  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 34.07/24.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.07/24.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 34.07/24.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 34.07/24.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.07/24.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 34.07/24.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 34.07/24.76  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 34.07/24.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 34.07/24.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 34.07/24.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 34.07/24.76  
% 34.41/24.79  tff(f_220, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 34.41/24.79  tff(f_176, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 34.41/24.79  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 34.41/24.79  tff(f_102, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 34.41/24.79  tff(f_61, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 34.41/24.79  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 34.41/24.79  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 34.41/24.79  tff(f_156, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 34.41/24.79  tff(f_128, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 34.41/24.79  tff(f_196, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 34.41/24.79  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 34.41/24.79  tff(f_95, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 34.41/24.79  tff(f_172, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 34.41/24.79  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 34.41/24.79  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 34.41/24.79  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 34.41/24.79  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 34.41/24.79  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 34.41/24.79  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 34.41/24.79  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 34.41/24.79  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 34.41/24.79  tff(f_184, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 34.41/24.79  tff(c_86, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 34.41/24.79  tff(c_84, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 34.41/24.79  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_220])).
% 34.41/24.79  tff(c_88, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_220])).
% 34.41/24.79  tff(c_120, plain, (![A_71]: (u1_struct_0(A_71)=k2_struct_0(A_71) | ~l1_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_176])).
% 34.41/24.79  tff(c_128, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_88, c_120])).
% 34.41/24.79  tff(c_127, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_84, c_120])).
% 34.41/24.79  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_220])).
% 34.41/24.79  tff(c_178, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_127, c_78])).
% 34.41/24.79  tff(c_193619, plain, (![A_6172, B_6173, C_6174]: (k2_relset_1(A_6172, B_6173, C_6174)=k2_relat_1(C_6174) | ~m1_subset_1(C_6174, k1_zfmisc_1(k2_zfmisc_1(A_6172, B_6173))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 34.41/24.79  tff(c_193633, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_178, c_193619])).
% 34.41/24.79  tff(c_76, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 34.41/24.79  tff(c_146, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_127, c_76])).
% 34.41/24.79  tff(c_193643, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_193633, c_146])).
% 34.41/24.79  tff(c_173357, plain, (![C_4969, B_4970, A_4971]: (v1_xboole_0(C_4969) | ~m1_subset_1(C_4969, k1_zfmisc_1(k2_zfmisc_1(B_4970, A_4971))) | ~v1_xboole_0(A_4971))), inference(cnfTransformation, [status(thm)], [f_102])).
% 34.41/24.79  tff(c_173371, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_178, c_173357])).
% 34.41/24.79  tff(c_173382, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_173371])).
% 34.41/24.79  tff(c_193650, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_193643, c_173382])).
% 34.41/24.79  tff(c_24, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 34.41/24.79  tff(c_22, plain, (![B_13, A_11]: (v1_relat_1(B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_11)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 34.41/24.79  tff(c_181, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_178, c_22])).
% 34.41/24.79  tff(c_190, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_181])).
% 34.41/24.79  tff(c_173185, plain, (![C_4937, A_4938, B_4939]: (v4_relat_1(C_4937, A_4938) | ~m1_subset_1(C_4937, k1_zfmisc_1(k2_zfmisc_1(A_4938, B_4939))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 34.41/24.79  tff(c_173199, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_178, c_173185])).
% 34.41/24.79  tff(c_193511, plain, (![B_6159, A_6160]: (k1_relat_1(B_6159)=A_6160 | ~v1_partfun1(B_6159, A_6160) | ~v4_relat_1(B_6159, A_6160) | ~v1_relat_1(B_6159))), inference(cnfTransformation, [status(thm)], [f_156])).
% 34.41/24.79  tff(c_193523, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_173199, c_193511])).
% 34.41/24.79  tff(c_193533, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_193523])).
% 34.41/24.79  tff(c_193562, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_193533])).
% 34.41/24.79  tff(c_80, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_220])).
% 34.41/24.79  tff(c_129, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_80])).
% 34.41/24.79  tff(c_139, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_129])).
% 34.41/24.79  tff(c_193658, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_193643, c_139])).
% 34.41/24.79  tff(c_193657, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_193643, c_178])).
% 34.41/24.79  tff(c_193809, plain, (![C_6180, A_6181, B_6182]: (v1_partfun1(C_6180, A_6181) | ~v1_funct_2(C_6180, A_6181, B_6182) | ~v1_funct_1(C_6180) | ~m1_subset_1(C_6180, k1_zfmisc_1(k2_zfmisc_1(A_6181, B_6182))) | v1_xboole_0(B_6182))), inference(cnfTransformation, [status(thm)], [f_128])).
% 34.41/24.79  tff(c_193812, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_193657, c_193809])).
% 34.41/24.79  tff(c_193829, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_193658, c_193812])).
% 34.41/24.79  tff(c_193831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_193650, c_193562, c_193829])).
% 34.41/24.79  tff(c_193832, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_193533])).
% 34.41/24.79  tff(c_193843, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_193832, c_178])).
% 34.41/24.79  tff(c_193993, plain, (![A_6189, B_6190, C_6191]: (k2_relset_1(A_6189, B_6190, C_6191)=k2_relat_1(C_6191) | ~m1_subset_1(C_6191, k1_zfmisc_1(k2_zfmisc_1(A_6189, B_6190))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 34.41/24.79  tff(c_194007, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_193843, c_193993])).
% 34.41/24.79  tff(c_193844, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_193832, c_146])).
% 34.41/24.79  tff(c_194119, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_194007, c_193844])).
% 34.41/24.79  tff(c_193845, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_193832, c_139])).
% 34.41/24.79  tff(c_194130, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_194119, c_193845])).
% 34.41/24.79  tff(c_194124, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_194119, c_194007])).
% 34.41/24.79  tff(c_74, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_220])).
% 34.41/24.79  tff(c_194126, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_194119, c_193843])).
% 34.41/24.79  tff(c_195408, plain, (![A_6277, B_6278, C_6279]: (k2_tops_2(A_6277, B_6278, C_6279)=k2_funct_1(C_6279) | ~v2_funct_1(C_6279) | k2_relset_1(A_6277, B_6278, C_6279)!=B_6278 | ~m1_subset_1(C_6279, k1_zfmisc_1(k2_zfmisc_1(A_6277, B_6278))) | ~v1_funct_2(C_6279, A_6277, B_6278) | ~v1_funct_1(C_6279))), inference(cnfTransformation, [status(thm)], [f_196])).
% 34.41/24.79  tff(c_195424, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_194126, c_195408])).
% 34.41/24.79  tff(c_195446, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_194130, c_194124, c_74, c_195424])).
% 34.41/24.79  tff(c_34562, plain, (![A_2071, B_2072, C_2073]: (k2_relset_1(A_2071, B_2072, C_2073)=k2_relat_1(C_2073) | ~m1_subset_1(C_2073, k1_zfmisc_1(k2_zfmisc_1(A_2071, B_2072))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 34.41/24.79  tff(c_34579, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_178, c_34562])).
% 34.41/24.79  tff(c_34617, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34579, c_146])).
% 34.41/24.79  tff(c_377, plain, (![C_121, B_122, A_123]: (v1_xboole_0(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(B_122, A_123))) | ~v1_xboole_0(A_123))), inference(cnfTransformation, [status(thm)], [f_102])).
% 34.41/24.79  tff(c_391, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_178, c_377])).
% 34.41/24.79  tff(c_430, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_391])).
% 34.41/24.79  tff(c_34624, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34617, c_430])).
% 34.41/24.79  tff(c_278, plain, (![C_106, A_107, B_108]: (v4_relat_1(C_106, A_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 34.41/24.79  tff(c_292, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_178, c_278])).
% 34.41/24.79  tff(c_448, plain, (![B_129, A_130]: (k1_relat_1(B_129)=A_130 | ~v1_partfun1(B_129, A_130) | ~v4_relat_1(B_129, A_130) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_156])).
% 34.41/24.79  tff(c_460, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_292, c_448])).
% 34.41/24.79  tff(c_470, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_460])).
% 34.41/24.79  tff(c_34415, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_470])).
% 34.41/24.79  tff(c_34631, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34617, c_139])).
% 34.41/24.79  tff(c_34630, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_34617, c_178])).
% 34.41/24.79  tff(c_35260, plain, (![C_2100, A_2101, B_2102]: (v1_partfun1(C_2100, A_2101) | ~v1_funct_2(C_2100, A_2101, B_2102) | ~v1_funct_1(C_2100) | ~m1_subset_1(C_2100, k1_zfmisc_1(k2_zfmisc_1(A_2101, B_2102))) | v1_xboole_0(B_2102))), inference(cnfTransformation, [status(thm)], [f_128])).
% 34.41/24.79  tff(c_35272, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_34630, c_35260])).
% 34.41/24.79  tff(c_35292, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_34631, c_35272])).
% 34.41/24.79  tff(c_35294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34624, c_34415, c_35292])).
% 34.41/24.79  tff(c_35295, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_470])).
% 34.41/24.79  tff(c_35306, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_35295, c_178])).
% 34.41/24.79  tff(c_44, plain, (![A_40, B_41, C_42]: (k2_relset_1(A_40, B_41, C_42)=k2_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 34.41/24.79  tff(c_35397, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_35306, c_44])).
% 34.41/24.79  tff(c_35307, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_35295, c_146])).
% 34.41/24.79  tff(c_35521, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_35397, c_35307])).
% 34.41/24.79  tff(c_35308, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_35295, c_139])).
% 34.41/24.79  tff(c_35538, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_35521, c_35308])).
% 34.41/24.79  tff(c_35531, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_35521, c_35397])).
% 34.41/24.79  tff(c_35536, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_35521, c_35306])).
% 34.41/24.79  tff(c_53583, plain, (![A_2546, B_2547, C_2548]: (k2_tops_2(A_2546, B_2547, C_2548)=k2_funct_1(C_2548) | ~v2_funct_1(C_2548) | k2_relset_1(A_2546, B_2547, C_2548)!=B_2547 | ~m1_subset_1(C_2548, k1_zfmisc_1(k2_zfmisc_1(A_2546, B_2547))) | ~v1_funct_2(C_2548, A_2546, B_2547) | ~v1_funct_1(C_2548))), inference(cnfTransformation, [status(thm)], [f_196])).
% 34.41/24.79  tff(c_53598, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_35536, c_53583])).
% 34.41/24.79  tff(c_53615, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_35538, c_35531, c_74, c_53598])).
% 34.41/24.79  tff(c_72, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 34.41/24.79  tff(c_217, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_128, c_127, c_127, c_128, c_128, c_127, c_127, c_72])).
% 34.41/24.79  tff(c_218, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_217])).
% 34.41/24.79  tff(c_35303, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_35295, c_35295, c_218])).
% 34.41/24.79  tff(c_35707, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_35521, c_35521, c_35521, c_35303])).
% 34.41/24.79  tff(c_53618, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_53615, c_35707])).
% 34.41/24.79  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 34.41/24.79  tff(c_431, plain, (![C_126, A_127, B_128]: (v1_xboole_0(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))) | ~v1_xboole_0(A_127))), inference(cnfTransformation, [status(thm)], [f_95])).
% 34.41/24.79  tff(c_445, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_178, c_431])).
% 34.41/24.79  tff(c_447, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_445])).
% 34.41/24.79  tff(c_35298, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_35295, c_447])).
% 34.41/24.79  tff(c_36334, plain, (![C_2147, A_2148, B_2149]: (v1_funct_1(k2_funct_1(C_2147)) | k2_relset_1(A_2148, B_2149, C_2147)!=B_2149 | ~v2_funct_1(C_2147) | ~m1_subset_1(C_2147, k1_zfmisc_1(k2_zfmisc_1(A_2148, B_2149))) | ~v1_funct_2(C_2147, A_2148, B_2149) | ~v1_funct_1(C_2147))), inference(cnfTransformation, [status(thm)], [f_172])).
% 34.41/24.79  tff(c_36349, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_35536, c_36334])).
% 34.41/24.79  tff(c_36366, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_35538, c_74, c_35531, c_36349])).
% 34.41/24.79  tff(c_28, plain, (![B_19, A_18]: (k7_relat_1(B_19, A_18)=B_19 | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 34.41/24.79  tff(c_296, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_292, c_28])).
% 34.41/24.79  tff(c_299, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_190, c_296])).
% 34.41/24.79  tff(c_26, plain, (![B_17, A_16]: (k2_relat_1(k7_relat_1(B_17, A_16))=k9_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 34.41/24.79  tff(c_303, plain, (k9_relat_1('#skF_3', k2_struct_0('#skF_1'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_299, c_26])).
% 34.41/24.79  tff(c_307, plain, (k9_relat_1('#skF_3', k2_struct_0('#skF_1'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_303])).
% 34.41/24.79  tff(c_35300, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_35295, c_307])).
% 34.41/24.79  tff(c_35570, plain, (![A_2109, B_2110]: (k9_relat_1(k2_funct_1(A_2109), k9_relat_1(A_2109, B_2110))=B_2110 | ~r1_tarski(B_2110, k1_relat_1(A_2109)) | ~v2_funct_1(A_2109) | ~v1_funct_1(A_2109) | ~v1_relat_1(A_2109))), inference(cnfTransformation, [status(thm)], [f_82])).
% 34.41/24.79  tff(c_35585, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_35300, c_35570])).
% 34.41/24.79  tff(c_35592, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_82, c_74, c_8, c_35585])).
% 34.41/24.79  tff(c_30, plain, (![A_20, B_22]: (k9_relat_1(k2_funct_1(A_20), k9_relat_1(A_20, B_22))=B_22 | ~r1_tarski(B_22, k1_relat_1(A_20)) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 34.41/24.79  tff(c_35662, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_35592, c_30])).
% 34.41/24.79  tff(c_36526, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36366, c_35662])).
% 34.41/24.79  tff(c_36527, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_36526])).
% 34.41/24.79  tff(c_36779, plain, (![C_2173, B_2174, A_2175]: (m1_subset_1(k2_funct_1(C_2173), k1_zfmisc_1(k2_zfmisc_1(B_2174, A_2175))) | k2_relset_1(A_2175, B_2174, C_2173)!=B_2174 | ~v2_funct_1(C_2173) | ~m1_subset_1(C_2173, k1_zfmisc_1(k2_zfmisc_1(A_2175, B_2174))) | ~v1_funct_2(C_2173, A_2175, B_2174) | ~v1_funct_1(C_2173))), inference(cnfTransformation, [status(thm)], [f_172])).
% 34.41/24.79  tff(c_36815, plain, (![C_2173, B_2174, A_2175]: (v1_relat_1(k2_funct_1(C_2173)) | ~v1_relat_1(k2_zfmisc_1(B_2174, A_2175)) | k2_relset_1(A_2175, B_2174, C_2173)!=B_2174 | ~v2_funct_1(C_2173) | ~m1_subset_1(C_2173, k1_zfmisc_1(k2_zfmisc_1(A_2175, B_2174))) | ~v1_funct_2(C_2173, A_2175, B_2174) | ~v1_funct_1(C_2173))), inference(resolution, [status(thm)], [c_36779, c_22])).
% 34.41/24.79  tff(c_53441, plain, (![C_2541, A_2542, B_2543]: (v1_relat_1(k2_funct_1(C_2541)) | k2_relset_1(A_2542, B_2543, C_2541)!=B_2543 | ~v2_funct_1(C_2541) | ~m1_subset_1(C_2541, k1_zfmisc_1(k2_zfmisc_1(A_2542, B_2543))) | ~v1_funct_2(C_2541, A_2542, B_2543) | ~v1_funct_1(C_2541))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_36815])).
% 34.41/24.79  tff(c_53499, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_35536, c_53441])).
% 34.41/24.79  tff(c_53519, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_35538, c_74, c_35531, c_53499])).
% 34.41/24.79  tff(c_53521, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36527, c_53519])).
% 34.41/24.79  tff(c_53523, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_36526])).
% 34.41/24.79  tff(c_53868, plain, (![C_2554, B_2555, A_2556]: (m1_subset_1(k2_funct_1(C_2554), k1_zfmisc_1(k2_zfmisc_1(B_2555, A_2556))) | k2_relset_1(A_2556, B_2555, C_2554)!=B_2555 | ~v2_funct_1(C_2554) | ~m1_subset_1(C_2554, k1_zfmisc_1(k2_zfmisc_1(A_2556, B_2555))) | ~v1_funct_2(C_2554, A_2556, B_2555) | ~v1_funct_1(C_2554))), inference(cnfTransformation, [status(thm)], [f_172])).
% 34.41/24.79  tff(c_34, plain, (![C_25, A_23, B_24]: (v4_relat_1(C_25, A_23) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 34.41/24.79  tff(c_105842, plain, (![C_3609, B_3610, A_3611]: (v4_relat_1(k2_funct_1(C_3609), B_3610) | k2_relset_1(A_3611, B_3610, C_3609)!=B_3610 | ~v2_funct_1(C_3609) | ~m1_subset_1(C_3609, k1_zfmisc_1(k2_zfmisc_1(A_3611, B_3610))) | ~v1_funct_2(C_3609, A_3611, B_3610) | ~v1_funct_1(C_3609))), inference(resolution, [status(thm)], [c_53868, c_34])).
% 34.41/24.79  tff(c_105900, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_35536, c_105842])).
% 34.41/24.79  tff(c_105920, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_35538, c_74, c_35531, c_105900])).
% 34.41/24.79  tff(c_58, plain, (![B_52, A_51]: (k1_relat_1(B_52)=A_51 | ~v1_partfun1(B_52, A_51) | ~v4_relat_1(B_52, A_51) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_156])).
% 34.41/24.79  tff(c_105925, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_105920, c_58])).
% 34.41/24.79  tff(c_105931, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_53523, c_105925])).
% 34.41/24.79  tff(c_106026, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_105931])).
% 34.41/24.79  tff(c_36462, plain, (![C_2161, B_2162, A_2163]: (v1_funct_2(k2_funct_1(C_2161), B_2162, A_2163) | k2_relset_1(A_2163, B_2162, C_2161)!=B_2162 | ~v2_funct_1(C_2161) | ~m1_subset_1(C_2161, k1_zfmisc_1(k2_zfmisc_1(A_2163, B_2162))) | ~v1_funct_2(C_2161, A_2163, B_2162) | ~v1_funct_1(C_2161))), inference(cnfTransformation, [status(thm)], [f_172])).
% 34.41/24.79  tff(c_36477, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_35536, c_36462])).
% 34.41/24.79  tff(c_36494, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_35538, c_74, c_35531, c_36477])).
% 34.41/24.79  tff(c_60, plain, (![C_55, B_54, A_53]: (m1_subset_1(k2_funct_1(C_55), k1_zfmisc_1(k2_zfmisc_1(B_54, A_53))) | k2_relset_1(A_53, B_54, C_55)!=B_54 | ~v2_funct_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_2(C_55, A_53, B_54) | ~v1_funct_1(C_55))), inference(cnfTransformation, [status(thm)], [f_172])).
% 34.41/24.79  tff(c_105928, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_105920, c_28])).
% 34.41/24.79  tff(c_105934, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_53523, c_105928])).
% 34.41/24.79  tff(c_105945, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_105934, c_26])).
% 34.41/24.79  tff(c_105955, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_53523, c_35592, c_105945])).
% 34.41/24.79  tff(c_118244, plain, (![B_3789, A_3790, C_3791]: (k2_relset_1(B_3789, A_3790, k2_funct_1(C_3791))=k2_relat_1(k2_funct_1(C_3791)) | k2_relset_1(A_3790, B_3789, C_3791)!=B_3789 | ~v2_funct_1(C_3791) | ~m1_subset_1(C_3791, k1_zfmisc_1(k2_zfmisc_1(A_3790, B_3789))) | ~v1_funct_2(C_3791, A_3790, B_3789) | ~v1_funct_1(C_3791))), inference(resolution, [status(thm)], [c_53868, c_44])).
% 34.41/24.79  tff(c_118314, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_35536, c_118244])).
% 34.41/24.79  tff(c_118334, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_35538, c_74, c_35531, c_105955, c_118314])).
% 34.41/24.79  tff(c_40, plain, (![A_34, B_35, C_36]: (m1_subset_1(k2_relset_1(A_34, B_35, C_36), k1_zfmisc_1(B_35)) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 34.41/24.79  tff(c_118346, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1(k1_relat_1('#skF_3'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_118334, c_40])).
% 34.41/24.79  tff(c_118356, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(splitLeft, [status(thm)], [c_118346])).
% 34.41/24.79  tff(c_118362, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_118356])).
% 34.41/24.79  tff(c_118369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_35538, c_35536, c_74, c_35531, c_118362])).
% 34.41/24.79  tff(c_118371, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_118346])).
% 34.41/24.79  tff(c_46, plain, (![C_46, A_43, B_44]: (v1_partfun1(C_46, A_43) | ~v1_funct_2(C_46, A_43, B_44) | ~v1_funct_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))) | v1_xboole_0(B_44))), inference(cnfTransformation, [status(thm)], [f_128])).
% 34.41/24.79  tff(c_118432, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | v1_xboole_0(k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_118371, c_46])).
% 34.41/24.79  tff(c_118509, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | v1_xboole_0(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36366, c_36494, c_118432])).
% 34.41/24.79  tff(c_118511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35298, c_106026, c_118509])).
% 34.41/24.79  tff(c_118512, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_105931])).
% 34.41/24.79  tff(c_73065, plain, (![C_2983, B_2984, A_2985]: (v4_relat_1(k2_funct_1(C_2983), B_2984) | k2_relset_1(A_2985, B_2984, C_2983)!=B_2984 | ~v2_funct_1(C_2983) | ~m1_subset_1(C_2983, k1_zfmisc_1(k2_zfmisc_1(A_2985, B_2984))) | ~v1_funct_2(C_2983, A_2985, B_2984) | ~v1_funct_1(C_2983))), inference(resolution, [status(thm)], [c_53868, c_34])).
% 34.41/24.79  tff(c_73123, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_35536, c_73065])).
% 34.41/24.79  tff(c_73143, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_35538, c_74, c_35531, c_73123])).
% 34.41/24.79  tff(c_73148, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_73143, c_58])).
% 34.41/24.79  tff(c_73154, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_53523, c_73148])).
% 34.41/24.79  tff(c_73312, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_73154])).
% 34.41/24.79  tff(c_73151, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_73143, c_28])).
% 34.41/24.79  tff(c_73157, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_53523, c_73151])).
% 34.41/24.79  tff(c_73168, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_73157, c_26])).
% 34.41/24.79  tff(c_73178, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_53523, c_35592, c_73168])).
% 34.41/24.79  tff(c_85140, plain, (![B_3159, A_3160, C_3161]: (k2_relset_1(B_3159, A_3160, k2_funct_1(C_3161))=k2_relat_1(k2_funct_1(C_3161)) | k2_relset_1(A_3160, B_3159, C_3161)!=B_3159 | ~v2_funct_1(C_3161) | ~m1_subset_1(C_3161, k1_zfmisc_1(k2_zfmisc_1(A_3160, B_3159))) | ~v1_funct_2(C_3161, A_3160, B_3159) | ~v1_funct_1(C_3161))), inference(resolution, [status(thm)], [c_53868, c_44])).
% 34.41/24.79  tff(c_85210, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_35536, c_85140])).
% 34.41/24.79  tff(c_85230, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_35538, c_74, c_35531, c_73178, c_85210])).
% 34.41/24.79  tff(c_85242, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1(k1_relat_1('#skF_3'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_85230, c_40])).
% 34.41/24.79  tff(c_85252, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(splitLeft, [status(thm)], [c_85242])).
% 34.41/24.79  tff(c_85258, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_85252])).
% 34.41/24.79  tff(c_85265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_35538, c_35536, c_74, c_35531, c_85258])).
% 34.41/24.79  tff(c_85267, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_85242])).
% 34.41/24.79  tff(c_85325, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | v1_xboole_0(k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_85267, c_46])).
% 34.41/24.79  tff(c_85399, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | v1_xboole_0(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36366, c_36494, c_85325])).
% 34.41/24.79  tff(c_85401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35298, c_73312, c_85399])).
% 34.41/24.79  tff(c_85402, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_73154])).
% 34.41/24.79  tff(c_53522, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_36526])).
% 34.41/24.79  tff(c_53971, plain, (~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_53522])).
% 34.41/24.79  tff(c_85404, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_85402, c_53971])).
% 34.41/24.79  tff(c_85407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_85404])).
% 34.41/24.79  tff(c_85409, plain, (r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_53522])).
% 34.41/24.79  tff(c_4, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 34.41/24.79  tff(c_85418, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_85409, c_4])).
% 34.41/24.79  tff(c_85604, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_85418])).
% 34.41/24.79  tff(c_118514, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_118512, c_85604])).
% 34.41/24.79  tff(c_118520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_118514])).
% 34.41/24.79  tff(c_118521, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_85418])).
% 34.41/24.79  tff(c_42, plain, (![A_37, B_38, C_39]: (k1_relset_1(A_37, B_38, C_39)=k1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 34.41/24.79  tff(c_171598, plain, (![B_4817, A_4818, C_4819]: (k1_relset_1(B_4817, A_4818, k2_funct_1(C_4819))=k1_relat_1(k2_funct_1(C_4819)) | k2_relset_1(A_4818, B_4817, C_4819)!=B_4817 | ~v2_funct_1(C_4819) | ~m1_subset_1(C_4819, k1_zfmisc_1(k2_zfmisc_1(A_4818, B_4817))) | ~v1_funct_2(C_4819, A_4818, B_4817) | ~v1_funct_1(C_4819))), inference(resolution, [status(thm)], [c_53868, c_42])).
% 34.41/24.79  tff(c_171668, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_35536, c_171598])).
% 34.41/24.79  tff(c_171688, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_35538, c_74, c_35531, c_118521, c_171668])).
% 34.41/24.79  tff(c_171690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53618, c_171688])).
% 34.41/24.79  tff(c_171691, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_445])).
% 34.41/24.79  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 34.41/24.79  tff(c_171696, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_171691, c_2])).
% 34.41/24.79  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 34.41/24.79  tff(c_171706, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171696, c_171696, c_14])).
% 34.41/24.79  tff(c_171692, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_445])).
% 34.41/24.79  tff(c_171738, plain, (![A_4822]: (A_4822='#skF_3' | ~v1_xboole_0(A_4822))), inference(demodulation, [status(thm), theory('equality')], [c_171696, c_2])).
% 34.41/24.79  tff(c_171745, plain, (k2_struct_0('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_171692, c_171738])).
% 34.41/24.79  tff(c_16, plain, (![B_8, A_6]: (v1_xboole_0(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 34.41/24.79  tff(c_191, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_178, c_16])).
% 34.41/24.79  tff(c_219, plain, (~v1_xboole_0(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_191])).
% 34.41/24.79  tff(c_171753, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_171745, c_219])).
% 34.41/24.79  tff(c_171929, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_171691, c_171706, c_171753])).
% 34.41/24.79  tff(c_171931, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_391])).
% 34.41/24.79  tff(c_68, plain, (![A_57]: (~v1_xboole_0(k2_struct_0(A_57)) | ~l1_struct_0(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_184])).
% 34.41/24.79  tff(c_171938, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_171931, c_68])).
% 34.41/24.79  tff(c_171944, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_171938])).
% 34.41/24.79  tff(c_171946, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_171944])).
% 34.41/24.79  tff(c_171947, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_191])).
% 34.41/24.79  tff(c_171948, plain, (v1_xboole_0(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_191])).
% 34.41/24.79  tff(c_171952, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_171947, c_2])).
% 34.41/24.79  tff(c_171957, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_171952, c_2])).
% 34.41/24.79  tff(c_172001, plain, (k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))='#skF_3'), inference(resolution, [status(thm)], [c_171948, c_171957])).
% 34.41/24.79  tff(c_172004, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_172001, c_178])).
% 34.41/24.79  tff(c_171954, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171952, c_171952, c_14])).
% 34.41/24.79  tff(c_172834, plain, (![A_4910, B_4911, C_4912]: (k2_relset_1(A_4910, B_4911, C_4912)=k2_relat_1(C_4912) | ~m1_subset_1(C_4912, k1_zfmisc_1(k2_zfmisc_1(A_4910, B_4911))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 34.41/24.79  tff(c_172973, plain, (![B_4928, C_4929]: (k2_relset_1('#skF_3', B_4928, C_4929)=k2_relat_1(C_4929) | ~m1_subset_1(C_4929, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_171954, c_172834])).
% 34.41/24.79  tff(c_172979, plain, (![B_4928]: (k2_relset_1('#skF_3', B_4928, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_172004, c_172973])).
% 34.41/24.79  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 34.41/24.79  tff(c_172033, plain, (![B_4836, A_4837]: (B_4836='#skF_3' | A_4837='#skF_3' | k2_zfmisc_1(A_4837, B_4836)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_171952, c_171952, c_171952, c_10])).
% 34.41/24.79  tff(c_172043, plain, (k2_struct_0('#skF_2')='#skF_3' | k2_struct_0('#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_172001, c_172033])).
% 34.41/24.79  tff(c_172048, plain, (k2_struct_0('#skF_1')='#skF_3'), inference(splitLeft, [status(thm)], [c_172043])).
% 34.41/24.79  tff(c_172051, plain, (k2_relset_1('#skF_3', k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_172048, c_146])).
% 34.41/24.79  tff(c_172981, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172979, c_172051])).
% 34.41/24.79  tff(c_173003, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_172981, c_68])).
% 34.41/24.79  tff(c_173007, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_173003])).
% 34.41/24.79  tff(c_173008, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_86, c_173007])).
% 34.41/24.79  tff(c_173020, plain, (![A_4933, B_4934, C_4935]: (m1_subset_1(k2_relset_1(A_4933, B_4934, C_4935), k1_zfmisc_1(B_4934)) | ~m1_subset_1(C_4935, k1_zfmisc_1(k2_zfmisc_1(A_4933, B_4934))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 34.41/24.79  tff(c_173072, plain, (![B_4928]: (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1(B_4928)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_4928))))), inference(superposition, [status(thm), theory('equality')], [c_172979, c_173020])).
% 34.41/24.79  tff(c_173099, plain, (![B_4936]: (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1(B_4936)))), inference(demodulation, [status(thm), theory('equality')], [c_172004, c_171954, c_173072])).
% 34.41/24.79  tff(c_172178, plain, (![C_4863, A_4864, B_4865]: (v1_xboole_0(C_4863) | ~m1_subset_1(C_4863, k1_zfmisc_1(k2_zfmisc_1(A_4864, B_4865))) | ~v1_xboole_0(A_4864))), inference(cnfTransformation, [status(thm)], [f_95])).
% 34.41/24.79  tff(c_172184, plain, (![C_4863]: (v1_xboole_0(C_4863) | ~m1_subset_1(C_4863, k1_zfmisc_1('#skF_3')) | ~v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_171954, c_172178])).
% 34.41/24.79  tff(c_172190, plain, (![C_4863]: (v1_xboole_0(C_4863) | ~m1_subset_1(C_4863, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_171947, c_172184])).
% 34.41/24.79  tff(c_173121, plain, (v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_173099, c_172190])).
% 34.41/24.79  tff(c_173159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173008, c_173121])).
% 34.41/24.79  tff(c_173160, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_172043])).
% 34.41/24.79  tff(c_173171, plain, (~v1_xboole_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_173160, c_68])).
% 34.41/24.79  tff(c_173175, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_171947, c_173171])).
% 34.41/24.79  tff(c_173177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_173175])).
% 34.41/24.79  tff(c_173178, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_217])).
% 34.41/24.79  tff(c_193838, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_193832, c_193832, c_193832, c_173178])).
% 34.41/24.80  tff(c_194361, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_194119, c_194119, c_193838])).
% 34.41/24.80  tff(c_195450, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_195446, c_194361])).
% 34.41/24.80  tff(c_195009, plain, (![C_6250, A_6251, B_6252]: (v1_funct_1(k2_funct_1(C_6250)) | k2_relset_1(A_6251, B_6252, C_6250)!=B_6252 | ~v2_funct_1(C_6250) | ~m1_subset_1(C_6250, k1_zfmisc_1(k2_zfmisc_1(A_6251, B_6252))) | ~v1_funct_2(C_6250, A_6251, B_6252) | ~v1_funct_1(C_6250))), inference(cnfTransformation, [status(thm)], [f_172])).
% 34.41/24.80  tff(c_195021, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_194126, c_195009])).
% 34.41/24.80  tff(c_195041, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_194130, c_74, c_194124, c_195021])).
% 34.41/24.80  tff(c_173265, plain, (![B_4957, A_4958]: (k7_relat_1(B_4957, A_4958)=B_4957 | ~v4_relat_1(B_4957, A_4958) | ~v1_relat_1(B_4957))), inference(cnfTransformation, [status(thm)], [f_71])).
% 34.41/24.80  tff(c_173277, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_173199, c_173265])).
% 34.41/24.80  tff(c_173287, plain, (k7_relat_1('#skF_3', k2_struct_0('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_190, c_173277])).
% 34.41/24.80  tff(c_193837, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_193832, c_173287])).
% 34.41/24.80  tff(c_193883, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_193837, c_26])).
% 34.41/24.80  tff(c_193887, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_193883])).
% 34.41/24.80  tff(c_194307, plain, (![A_6202, B_6203]: (k9_relat_1(k2_funct_1(A_6202), k9_relat_1(A_6202, B_6203))=B_6203 | ~r1_tarski(B_6203, k1_relat_1(A_6202)) | ~v2_funct_1(A_6202) | ~v1_funct_1(A_6202) | ~v1_relat_1(A_6202))), inference(cnfTransformation, [status(thm)], [f_82])).
% 34.41/24.80  tff(c_194322, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_193887, c_194307])).
% 34.41/24.80  tff(c_194329, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_82, c_74, c_8, c_194322])).
% 34.41/24.80  tff(c_194335, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_194329, c_30])).
% 34.41/24.80  tff(c_195460, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_195041, c_194335])).
% 34.41/24.80  tff(c_195461, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_195460])).
% 34.41/24.80  tff(c_195826, plain, (![C_6291, B_6292, A_6293]: (m1_subset_1(k2_funct_1(C_6291), k1_zfmisc_1(k2_zfmisc_1(B_6292, A_6293))) | k2_relset_1(A_6293, B_6292, C_6291)!=B_6292 | ~v2_funct_1(C_6291) | ~m1_subset_1(C_6291, k1_zfmisc_1(k2_zfmisc_1(A_6293, B_6292))) | ~v1_funct_2(C_6291, A_6293, B_6292) | ~v1_funct_1(C_6291))), inference(cnfTransformation, [status(thm)], [f_172])).
% 34.41/24.80  tff(c_195862, plain, (![C_6291, B_6292, A_6293]: (v1_relat_1(k2_funct_1(C_6291)) | ~v1_relat_1(k2_zfmisc_1(B_6292, A_6293)) | k2_relset_1(A_6293, B_6292, C_6291)!=B_6292 | ~v2_funct_1(C_6291) | ~m1_subset_1(C_6291, k1_zfmisc_1(k2_zfmisc_1(A_6293, B_6292))) | ~v1_funct_2(C_6291, A_6293, B_6292) | ~v1_funct_1(C_6291))), inference(resolution, [status(thm)], [c_195826, c_22])).
% 34.41/24.80  tff(c_211499, plain, (![C_6623, A_6624, B_6625]: (v1_relat_1(k2_funct_1(C_6623)) | k2_relset_1(A_6624, B_6625, C_6623)!=B_6625 | ~v2_funct_1(C_6623) | ~m1_subset_1(C_6623, k1_zfmisc_1(k2_zfmisc_1(A_6624, B_6625))) | ~v1_funct_2(C_6623, A_6624, B_6625) | ~v1_funct_1(C_6623))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_195862])).
% 34.41/24.80  tff(c_211554, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_194126, c_211499])).
% 34.41/24.80  tff(c_211577, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_194130, c_74, c_194124, c_211554])).
% 34.41/24.80  tff(c_211579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195461, c_211577])).
% 34.41/24.80  tff(c_211581, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_195460])).
% 34.41/24.80  tff(c_212105, plain, (![C_6643, B_6644, A_6645]: (m1_subset_1(k2_funct_1(C_6643), k1_zfmisc_1(k2_zfmisc_1(B_6644, A_6645))) | k2_relset_1(A_6645, B_6644, C_6643)!=B_6644 | ~v2_funct_1(C_6643) | ~m1_subset_1(C_6643, k1_zfmisc_1(k2_zfmisc_1(A_6645, B_6644))) | ~v1_funct_2(C_6643, A_6645, B_6644) | ~v1_funct_1(C_6643))), inference(cnfTransformation, [status(thm)], [f_172])).
% 34.41/24.80  tff(c_234603, plain, (![C_7095, B_7096, A_7097]: (v4_relat_1(k2_funct_1(C_7095), B_7096) | k2_relset_1(A_7097, B_7096, C_7095)!=B_7096 | ~v2_funct_1(C_7095) | ~m1_subset_1(C_7095, k1_zfmisc_1(k2_zfmisc_1(A_7097, B_7096))) | ~v1_funct_2(C_7095, A_7097, B_7096) | ~v1_funct_1(C_7095))), inference(resolution, [status(thm)], [c_212105, c_34])).
% 34.41/24.80  tff(c_234658, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_194126, c_234603])).
% 34.41/24.80  tff(c_234681, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_194130, c_74, c_194124, c_234658])).
% 34.41/24.80  tff(c_234689, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_234681, c_28])).
% 34.41/24.80  tff(c_234695, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_211581, c_234689])).
% 34.41/24.80  tff(c_234706, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_234695, c_26])).
% 34.41/24.80  tff(c_234716, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_211581, c_194329, c_234706])).
% 34.41/24.80  tff(c_244727, plain, (![B_7234, A_7235, C_7236]: (k2_relset_1(B_7234, A_7235, k2_funct_1(C_7236))=k2_relat_1(k2_funct_1(C_7236)) | k2_relset_1(A_7235, B_7234, C_7236)!=B_7234 | ~v2_funct_1(C_7236) | ~m1_subset_1(C_7236, k1_zfmisc_1(k2_zfmisc_1(A_7235, B_7234))) | ~v1_funct_2(C_7236, A_7235, B_7234) | ~v1_funct_1(C_7236))), inference(resolution, [status(thm)], [c_212105, c_44])).
% 34.41/24.80  tff(c_244794, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_194126, c_244727])).
% 34.41/24.80  tff(c_244817, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_194130, c_74, c_194124, c_234716, c_244794])).
% 34.41/24.80  tff(c_244819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195450, c_244817])).
% 34.41/24.80  tff(c_244821, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_173371])).
% 34.41/24.80  tff(c_244847, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_244821, c_68])).
% 34.41/24.80  tff(c_244850, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_244847])).
% 34.41/24.80  tff(c_244852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_244850])).
% 34.41/24.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.41/24.80  
% 34.41/24.80  Inference rules
% 34.41/24.80  ----------------------
% 34.41/24.80  #Ref     : 0
% 34.41/24.80  #Sup     : 58606
% 34.41/24.80  #Fact    : 0
% 34.41/24.80  #Define  : 0
% 34.41/24.80  #Split   : 143
% 34.41/24.80  #Chain   : 0
% 34.41/24.80  #Close   : 0
% 34.41/24.80  
% 34.41/24.80  Ordering : KBO
% 34.41/24.80  
% 34.41/24.80  Simplification rules
% 34.41/24.80  ----------------------
% 34.41/24.80  #Subsume      : 19556
% 34.41/24.80  #Demod        : 65477
% 34.41/24.80  #Tautology    : 31099
% 34.41/24.80  #SimpNegUnit  : 1876
% 34.41/24.80  #BackRed      : 899
% 34.41/24.80  
% 34.41/24.80  #Partial instantiations: 0
% 34.41/24.80  #Strategies tried      : 1
% 34.41/24.80  
% 34.41/24.80  Timing (in seconds)
% 34.41/24.80  ----------------------
% 34.41/24.80  Preprocessing        : 0.37
% 34.41/24.80  Parsing              : 0.20
% 34.41/24.80  CNF conversion       : 0.03
% 34.41/24.80  Main loop            : 23.60
% 34.41/24.80  Inferencing          : 5.08
% 34.41/24.80  Reduction            : 9.59
% 34.41/24.80  Demodulation         : 7.60
% 34.41/24.80  BG Simplification    : 0.51
% 34.41/24.80  Subsumption          : 7.34
% 34.41/24.80  Abstraction          : 0.85
% 34.41/24.80  MUC search           : 0.00
% 34.41/24.80  Cooper               : 0.00
% 34.41/24.80  Total                : 24.08
% 34.41/24.80  Index Insertion      : 0.00
% 34.41/24.80  Index Deletion       : 0.00
% 34.41/24.80  Index Matching       : 0.00
% 34.41/24.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
