%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:13 EST 2020

% Result     : Theorem 5.09s
% Output     : CNFRefutation 5.32s
% Verified   : 
% Statistics : Number of formulae       :  206 (6558 expanded)
%              Number of leaves         :   43 (2310 expanded)
%              Depth                    :   20
%              Number of atoms          :  446 (20370 expanded)
%              Number of equality atoms :   89 (6545 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_176,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_132,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_152,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_110,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

tff(c_74,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_76,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_84,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_76])).

tff(c_70,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_83,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_76])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_105,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83,c_64])).

tff(c_16,plain,(
    ! [C_10,A_8,B_9] :
      ( v1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_112,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_16])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_funct_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_12,plain,(
    ! [A_7] :
      ( k2_relat_1(k2_funct_1(A_7)) = k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_6] :
      ( v1_relat_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_7] :
      ( k1_relat_1(k2_funct_1(A_7)) = k2_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1997,plain,(
    ! [A_243] :
      ( m1_subset_1(A_243,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_243),k2_relat_1(A_243))))
      | ~ v1_funct_1(A_243)
      | ~ v1_relat_1(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2328,plain,(
    ! [A_284] :
      ( m1_subset_1(k2_funct_1(A_284),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_284),k2_relat_1(k2_funct_1(A_284)))))
      | ~ v1_funct_1(k2_funct_1(A_284))
      | ~ v1_relat_1(k2_funct_1(A_284))
      | ~ v2_funct_1(A_284)
      | ~ v1_funct_1(A_284)
      | ~ v1_relat_1(A_284) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1997])).

tff(c_2545,plain,(
    ! [A_295] :
      ( m1_subset_1(k2_funct_1(A_295),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_295),k1_relat_1(A_295))))
      | ~ v1_funct_1(k2_funct_1(A_295))
      | ~ v1_relat_1(k2_funct_1(A_295))
      | ~ v2_funct_1(A_295)
      | ~ v1_funct_1(A_295)
      | ~ v1_relat_1(A_295)
      | ~ v2_funct_1(A_295)
      | ~ v1_funct_1(A_295)
      | ~ v1_relat_1(A_295) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2328])).

tff(c_22,plain,(
    ! [A_14,B_15,C_16] :
      ( k2_relset_1(A_14,B_15,C_16) = k2_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2594,plain,(
    ! [A_296] :
      ( k2_relset_1(k2_relat_1(A_296),k1_relat_1(A_296),k2_funct_1(A_296)) = k2_relat_1(k2_funct_1(A_296))
      | ~ v1_funct_1(k2_funct_1(A_296))
      | ~ v1_relat_1(k2_funct_1(A_296))
      | ~ v2_funct_1(A_296)
      | ~ v1_funct_1(A_296)
      | ~ v1_relat_1(A_296) ) ),
    inference(resolution,[status(thm)],[c_2545,c_22])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1752,plain,(
    ! [A_219,B_220,C_221] :
      ( k2_relset_1(A_219,B_220,C_221) = k2_relat_1(C_221)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1756,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_1752])).

tff(c_62,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_99,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83,c_62])).

tff(c_1757,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1756,c_99])).

tff(c_54,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(k2_struct_0(A_32))
      | ~ l1_struct_0(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1773,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1757,c_54])).

tff(c_1777,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1773])).

tff(c_1778,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1777])).

tff(c_1705,plain,(
    ! [C_207,A_208,B_209] :
      ( v4_relat_1(C_207,A_208)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1709,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_105,c_1705])).

tff(c_1729,plain,(
    ! [B_216,A_217] :
      ( k1_relat_1(B_216) = A_217
      | ~ v1_partfun1(B_216,A_217)
      | ~ v4_relat_1(B_216,A_217)
      | ~ v1_relat_1(B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1732,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1709,c_1729])).

tff(c_1735,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_1732])).

tff(c_1736,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1735])).

tff(c_66,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_89,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_66])).

tff(c_90,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_89])).

tff(c_1768,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1757,c_90])).

tff(c_1767,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1757,c_105])).

tff(c_1907,plain,(
    ! [C_239,A_240,B_241] :
      ( v1_partfun1(C_239,A_240)
      | ~ v1_funct_2(C_239,A_240,B_241)
      | ~ v1_funct_1(C_239)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241)))
      | v1_xboole_0(B_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1913,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1767,c_1907])).

tff(c_1917,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1768,c_1913])).

tff(c_1919,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1778,c_1736,c_1917])).

tff(c_1920,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1735])).

tff(c_1925,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1920,c_105])).

tff(c_2048,plain,(
    ! [A_248,B_249,C_250] :
      ( k2_relset_1(A_248,B_249,C_250) = k2_relat_1(C_250)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2056,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1925,c_2048])).

tff(c_1926,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1920,c_99])).

tff(c_2057,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2056,c_1926])).

tff(c_1927,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1920,c_90])).

tff(c_2078,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_1927])).

tff(c_2075,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_2056])).

tff(c_2077,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_1925])).

tff(c_2225,plain,(
    ! [A_272,B_273,C_274] :
      ( k2_tops_2(A_272,B_273,C_274) = k2_funct_1(C_274)
      | ~ v2_funct_1(C_274)
      | k2_relset_1(A_272,B_273,C_274) != B_273
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273)))
      | ~ v1_funct_2(C_274,A_272,B_273)
      | ~ v1_funct_1(C_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2228,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2077,c_2225])).

tff(c_2234,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2078,c_2075,c_60,c_2228])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_427,plain,(
    ! [A_93] :
      ( k1_relat_1(k2_funct_1(A_93)) = k2_relat_1(A_93)
      | ~ v2_funct_1(A_93)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    ! [A_30] :
      ( v1_funct_2(A_30,k1_relat_1(A_30),k2_relat_1(A_30))
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_672,plain,(
    ! [A_127] :
      ( v1_funct_2(k2_funct_1(A_127),k2_relat_1(A_127),k2_relat_1(k2_funct_1(A_127)))
      | ~ v1_funct_1(k2_funct_1(A_127))
      | ~ v1_relat_1(k2_funct_1(A_127))
      | ~ v2_funct_1(A_127)
      | ~ v1_funct_1(A_127)
      | ~ v1_relat_1(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_48])).

tff(c_678,plain,(
    ! [A_7] :
      ( v1_funct_2(k2_funct_1(A_7),k2_relat_1(A_7),k1_relat_1(A_7))
      | ~ v1_funct_1(k2_funct_1(A_7))
      | ~ v1_relat_1(k2_funct_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_672])).

tff(c_467,plain,(
    ! [A_97] :
      ( m1_subset_1(A_97,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_97),k2_relat_1(A_97))))
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_750,plain,(
    ! [A_135] :
      ( m1_subset_1(k2_funct_1(A_135),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_135),k2_relat_1(k2_funct_1(A_135)))))
      | ~ v1_funct_1(k2_funct_1(A_135))
      | ~ v1_relat_1(k2_funct_1(A_135))
      | ~ v2_funct_1(A_135)
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_467])).

tff(c_967,plain,(
    ! [A_146] :
      ( m1_subset_1(k2_funct_1(A_146),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_146),k1_relat_1(A_146))))
      | ~ v1_funct_1(k2_funct_1(A_146))
      | ~ v1_relat_1(k2_funct_1(A_146))
      | ~ v2_funct_1(A_146)
      | ~ v1_funct_1(A_146)
      | ~ v1_relat_1(A_146)
      | ~ v2_funct_1(A_146)
      | ~ v1_funct_1(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_750])).

tff(c_40,plain,(
    ! [B_26,A_25,C_27] :
      ( k1_xboole_0 = B_26
      | k1_relset_1(A_25,B_26,C_27) = A_25
      | ~ v1_funct_2(C_27,A_25,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1084,plain,(
    ! [A_154] :
      ( k1_relat_1(A_154) = k1_xboole_0
      | k1_relset_1(k2_relat_1(A_154),k1_relat_1(A_154),k2_funct_1(A_154)) = k2_relat_1(A_154)
      | ~ v1_funct_2(k2_funct_1(A_154),k2_relat_1(A_154),k1_relat_1(A_154))
      | ~ v1_funct_1(k2_funct_1(A_154))
      | ~ v1_relat_1(k2_funct_1(A_154))
      | ~ v2_funct_1(A_154)
      | ~ v1_funct_1(A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(resolution,[status(thm)],[c_967,c_40])).

tff(c_1095,plain,(
    ! [A_155] :
      ( k1_relat_1(A_155) = k1_xboole_0
      | k1_relset_1(k2_relat_1(A_155),k1_relat_1(A_155),k2_funct_1(A_155)) = k2_relat_1(A_155)
      | ~ v1_funct_1(k2_funct_1(A_155))
      | ~ v1_relat_1(k2_funct_1(A_155))
      | ~ v2_funct_1(A_155)
      | ~ v1_funct_1(A_155)
      | ~ v1_relat_1(A_155) ) ),
    inference(resolution,[status(thm)],[c_678,c_1084])).

tff(c_166,plain,(
    ! [A_63,B_64,C_65] :
      ( k2_relset_1(A_63,B_64,C_65) = k2_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_170,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_166])).

tff(c_221,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_99])).

tff(c_235,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_54])).

tff(c_239,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_235])).

tff(c_240,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_239])).

tff(c_124,plain,(
    ! [C_54,A_55,B_56] :
      ( v4_relat_1(C_54,A_55)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_128,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_105,c_124])).

tff(c_131,plain,(
    ! [B_59,A_60] :
      ( k1_relat_1(B_59) = A_60
      | ~ v1_partfun1(B_59,A_60)
      | ~ v4_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_134,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_128,c_131])).

tff(c_137,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_134])).

tff(c_138,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_230,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_90])).

tff(c_229,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_105])).

tff(c_342,plain,(
    ! [C_89,A_90,B_91] :
      ( v1_partfun1(C_89,A_90)
      | ~ v1_funct_2(C_89,A_90,B_91)
      | ~ v1_funct_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | v1_xboole_0(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_345,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_229,c_342])).

tff(c_351,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_230,c_345])).

tff(c_353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_138,c_351])).

tff(c_354,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_358,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_105])).

tff(c_442,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_relset_1(A_94,B_95,C_96) = k2_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_446,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_358,c_442])).

tff(c_359,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_99])).

tff(c_447,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_359])).

tff(c_360,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_90])).

tff(c_454,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_360])).

tff(c_452,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_446])).

tff(c_453,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_358])).

tff(c_679,plain,(
    ! [A_128,B_129,C_130] :
      ( k2_tops_2(A_128,B_129,C_130) = k2_funct_1(C_130)
      | ~ v2_funct_1(C_130)
      | k2_relset_1(A_128,B_129,C_130) != B_129
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ v1_funct_2(C_130,A_128,B_129)
      | ~ v1_funct_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_682,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_453,c_679])).

tff(c_688,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_454,c_452,c_60,c_682])).

tff(c_58,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_116,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_84,c_83,c_83,c_84,c_84,c_83,c_83,c_58])).

tff(c_117,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_356,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_354,c_117])).

tff(c_591,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_447,c_447,c_356])).

tff(c_690,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_591])).

tff(c_1101,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1095,c_690])).

tff(c_1114,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_68,c_60,c_1101])).

tff(c_1116,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1114])).

tff(c_1119,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_1116])).

tff(c_1123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_68,c_1119])).

tff(c_1124,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1114])).

tff(c_1126,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1124])).

tff(c_1136,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_1126])).

tff(c_1140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_68,c_1136])).

tff(c_1141,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1124])).

tff(c_365,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_54])).

tff(c_369,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_365])).

tff(c_401,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_369])).

tff(c_1149,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1141,c_401])).

tff(c_1156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1149])).

tff(c_1158,plain,(
    v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_1258,plain,(
    ! [A_161] :
      ( m1_subset_1(A_161,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_161),k2_relat_1(A_161))))
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_20,plain,(
    ! [C_13,A_11,B_12] :
      ( v4_relat_1(C_13,A_11)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1288,plain,(
    ! [A_163] :
      ( v4_relat_1(A_163,k1_relat_1(A_163))
      | ~ v1_funct_1(A_163)
      | ~ v1_relat_1(A_163) ) ),
    inference(resolution,[status(thm)],[c_1258,c_20])).

tff(c_42,plain,(
    ! [B_29] :
      ( v1_partfun1(B_29,k1_relat_1(B_29))
      | ~ v4_relat_1(B_29,k1_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1300,plain,(
    ! [A_163] :
      ( v1_partfun1(A_163,k1_relat_1(A_163))
      | ~ v1_funct_1(A_163)
      | ~ v1_relat_1(A_163) ) ),
    inference(resolution,[status(thm)],[c_1288,c_42])).

tff(c_46,plain,(
    ! [A_30] :
      ( m1_subset_1(A_30,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_30),k2_relat_1(A_30))))
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1337,plain,(
    ! [C_167,A_168,B_169] :
      ( ~ v1_partfun1(C_167,A_168)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ v1_xboole_0(B_169)
      | v1_xboole_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1349,plain,(
    ! [A_172] :
      ( ~ v1_partfun1(A_172,k1_relat_1(A_172))
      | ~ v1_xboole_0(k2_relat_1(A_172))
      | v1_xboole_0(k1_relat_1(A_172))
      | ~ v1_funct_1(A_172)
      | ~ v1_relat_1(A_172) ) ),
    inference(resolution,[status(thm)],[c_46,c_1337])).

tff(c_1363,plain,(
    ! [A_173] :
      ( ~ v1_xboole_0(k2_relat_1(A_173))
      | v1_xboole_0(k1_relat_1(A_173))
      | ~ v1_funct_1(A_173)
      | ~ v1_relat_1(A_173) ) ),
    inference(resolution,[status(thm)],[c_1300,c_1349])).

tff(c_1440,plain,(
    ! [A_193] :
      ( ~ v1_xboole_0(k1_relat_1(A_193))
      | v1_xboole_0(k1_relat_1(k2_funct_1(A_193)))
      | ~ v1_funct_1(k2_funct_1(A_193))
      | ~ v1_relat_1(k2_funct_1(A_193))
      | ~ v2_funct_1(A_193)
      | ~ v1_funct_1(A_193)
      | ~ v1_relat_1(A_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1363])).

tff(c_1646,plain,(
    ! [A_205] :
      ( ~ v1_xboole_0(k1_relat_1(A_205))
      | v1_xboole_0(k2_relat_1(A_205))
      | ~ v1_funct_1(k2_funct_1(A_205))
      | ~ v1_relat_1(k2_funct_1(A_205))
      | ~ v2_funct_1(A_205)
      | ~ v1_funct_1(A_205)
      | ~ v1_relat_1(A_205)
      | ~ v2_funct_1(A_205)
      | ~ v1_funct_1(A_205)
      | ~ v1_relat_1(A_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1440])).

tff(c_1199,plain,(
    ! [A_158,B_159,C_160] :
      ( k2_relset_1(A_158,B_159,C_160) = k2_relat_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1203,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_358,c_1199])).

tff(c_1204,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1203,c_359])).

tff(c_1217,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1204,c_54])).

tff(c_1221,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1217])).

tff(c_1222,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1221])).

tff(c_1655,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1646,c_1222])).

tff(c_1663,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_68,c_60,c_1158,c_1655])).

tff(c_1664,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1663])).

tff(c_1667,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_1664])).

tff(c_1671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_68,c_1667])).

tff(c_1672,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1663])).

tff(c_1693,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_1672])).

tff(c_1697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_68,c_1693])).

tff(c_1698,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_1922,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1920,c_1920,c_1920,c_1698])).

tff(c_2160,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_2057,c_1922])).

tff(c_2237,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2234,c_2160])).

tff(c_2600,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2594,c_2237])).

tff(c_2612,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_68,c_60,c_2600])).

tff(c_2614,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2612])).

tff(c_2617,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_2614])).

tff(c_2621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_68,c_2617])).

tff(c_2622,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2612])).

tff(c_2624,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2622])).

tff(c_2627,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2624])).

tff(c_2631,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_68,c_60,c_2627])).

tff(c_2632,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2622])).

tff(c_2636,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_2632])).

tff(c_2640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_68,c_2636])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n007.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 18:03:21 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.09/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/1.93  
% 5.24/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.32/1.93  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.32/1.93  
% 5.32/1.93  %Foreground sorts:
% 5.32/1.93  
% 5.32/1.93  
% 5.32/1.93  %Background operators:
% 5.32/1.93  
% 5.32/1.93  
% 5.32/1.93  %Foreground operators:
% 5.32/1.93  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.32/1.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.32/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.32/1.93  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.32/1.93  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.32/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.32/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.32/1.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.32/1.93  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 5.32/1.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.32/1.93  tff('#skF_2', type, '#skF_2': $i).
% 5.32/1.93  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.32/1.93  tff('#skF_3', type, '#skF_3': $i).
% 5.32/1.93  tff('#skF_1', type, '#skF_1': $i).
% 5.32/1.93  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.32/1.93  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.32/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.32/1.93  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.32/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.32/1.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.32/1.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.32/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.32/1.93  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.32/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.32/1.93  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.32/1.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.32/1.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.32/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.32/1.93  
% 5.32/1.96  tff(f_176, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 5.32/1.96  tff(f_132, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.32/1.96  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.32/1.96  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.32/1.96  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.32/1.96  tff(f_128, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.32/1.96  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.32/1.96  tff(f_140, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 5.32/1.96  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.32/1.96  tff(f_118, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 5.32/1.96  tff(f_92, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 5.32/1.96  tff(f_152, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 5.32/1.96  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.32/1.96  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.32/1.96  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_partfun1)).
% 5.32/1.96  tff(c_74, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.32/1.96  tff(c_76, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.32/1.96  tff(c_84, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_74, c_76])).
% 5.32/1.96  tff(c_70, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.32/1.96  tff(c_83, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_76])).
% 5.32/1.96  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.32/1.96  tff(c_105, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83, c_64])).
% 5.32/1.96  tff(c_16, plain, (![C_10, A_8, B_9]: (v1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.32/1.96  tff(c_112, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_105, c_16])).
% 5.32/1.96  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.32/1.96  tff(c_8, plain, (![A_6]: (v1_funct_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.32/1.96  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.32/1.96  tff(c_12, plain, (![A_7]: (k2_relat_1(k2_funct_1(A_7))=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.32/1.96  tff(c_10, plain, (![A_6]: (v1_relat_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.32/1.96  tff(c_14, plain, (![A_7]: (k1_relat_1(k2_funct_1(A_7))=k2_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.32/1.96  tff(c_1997, plain, (![A_243]: (m1_subset_1(A_243, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_243), k2_relat_1(A_243)))) | ~v1_funct_1(A_243) | ~v1_relat_1(A_243))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.32/1.96  tff(c_2328, plain, (![A_284]: (m1_subset_1(k2_funct_1(A_284), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_284), k2_relat_1(k2_funct_1(A_284))))) | ~v1_funct_1(k2_funct_1(A_284)) | ~v1_relat_1(k2_funct_1(A_284)) | ~v2_funct_1(A_284) | ~v1_funct_1(A_284) | ~v1_relat_1(A_284))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1997])).
% 5.32/1.96  tff(c_2545, plain, (![A_295]: (m1_subset_1(k2_funct_1(A_295), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_295), k1_relat_1(A_295)))) | ~v1_funct_1(k2_funct_1(A_295)) | ~v1_relat_1(k2_funct_1(A_295)) | ~v2_funct_1(A_295) | ~v1_funct_1(A_295) | ~v1_relat_1(A_295) | ~v2_funct_1(A_295) | ~v1_funct_1(A_295) | ~v1_relat_1(A_295))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2328])).
% 5.32/1.96  tff(c_22, plain, (![A_14, B_15, C_16]: (k2_relset_1(A_14, B_15, C_16)=k2_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.32/1.96  tff(c_2594, plain, (![A_296]: (k2_relset_1(k2_relat_1(A_296), k1_relat_1(A_296), k2_funct_1(A_296))=k2_relat_1(k2_funct_1(A_296)) | ~v1_funct_1(k2_funct_1(A_296)) | ~v1_relat_1(k2_funct_1(A_296)) | ~v2_funct_1(A_296) | ~v1_funct_1(A_296) | ~v1_relat_1(A_296))), inference(resolution, [status(thm)], [c_2545, c_22])).
% 5.32/1.96  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.32/1.96  tff(c_1752, plain, (![A_219, B_220, C_221]: (k2_relset_1(A_219, B_220, C_221)=k2_relat_1(C_221) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.32/1.96  tff(c_1756, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_105, c_1752])).
% 5.32/1.96  tff(c_62, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.32/1.96  tff(c_99, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83, c_62])).
% 5.32/1.96  tff(c_1757, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1756, c_99])).
% 5.32/1.96  tff(c_54, plain, (![A_32]: (~v1_xboole_0(k2_struct_0(A_32)) | ~l1_struct_0(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.32/1.96  tff(c_1773, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1757, c_54])).
% 5.32/1.96  tff(c_1777, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1773])).
% 5.32/1.96  tff(c_1778, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_1777])).
% 5.32/1.96  tff(c_1705, plain, (![C_207, A_208, B_209]: (v4_relat_1(C_207, A_208) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.32/1.96  tff(c_1709, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_105, c_1705])).
% 5.32/1.96  tff(c_1729, plain, (![B_216, A_217]: (k1_relat_1(B_216)=A_217 | ~v1_partfun1(B_216, A_217) | ~v4_relat_1(B_216, A_217) | ~v1_relat_1(B_216))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.32/1.96  tff(c_1732, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1709, c_1729])).
% 5.32/1.96  tff(c_1735, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_1732])).
% 5.32/1.96  tff(c_1736, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1735])).
% 5.32/1.96  tff(c_66, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.32/1.96  tff(c_89, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_66])).
% 5.32/1.96  tff(c_90, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_89])).
% 5.32/1.96  tff(c_1768, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1757, c_90])).
% 5.32/1.96  tff(c_1767, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1757, c_105])).
% 5.32/1.96  tff(c_1907, plain, (![C_239, A_240, B_241]: (v1_partfun1(C_239, A_240) | ~v1_funct_2(C_239, A_240, B_241) | ~v1_funct_1(C_239) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))) | v1_xboole_0(B_241))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.32/1.96  tff(c_1913, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1767, c_1907])).
% 5.32/1.96  tff(c_1917, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1768, c_1913])).
% 5.32/1.96  tff(c_1919, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1778, c_1736, c_1917])).
% 5.32/1.96  tff(c_1920, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1735])).
% 5.32/1.96  tff(c_1925, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1920, c_105])).
% 5.32/1.96  tff(c_2048, plain, (![A_248, B_249, C_250]: (k2_relset_1(A_248, B_249, C_250)=k2_relat_1(C_250) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.32/1.96  tff(c_2056, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1925, c_2048])).
% 5.32/1.96  tff(c_1926, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1920, c_99])).
% 5.32/1.96  tff(c_2057, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2056, c_1926])).
% 5.32/1.96  tff(c_1927, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1920, c_90])).
% 5.32/1.96  tff(c_2078, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2057, c_1927])).
% 5.32/1.96  tff(c_2075, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2057, c_2056])).
% 5.32/1.96  tff(c_2077, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2057, c_1925])).
% 5.32/1.96  tff(c_2225, plain, (![A_272, B_273, C_274]: (k2_tops_2(A_272, B_273, C_274)=k2_funct_1(C_274) | ~v2_funct_1(C_274) | k2_relset_1(A_272, B_273, C_274)!=B_273 | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))) | ~v1_funct_2(C_274, A_272, B_273) | ~v1_funct_1(C_274))), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.32/1.96  tff(c_2228, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2077, c_2225])).
% 5.32/1.96  tff(c_2234, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2078, c_2075, c_60, c_2228])).
% 5.32/1.96  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.32/1.96  tff(c_427, plain, (![A_93]: (k1_relat_1(k2_funct_1(A_93))=k2_relat_1(A_93) | ~v2_funct_1(A_93) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.32/1.96  tff(c_48, plain, (![A_30]: (v1_funct_2(A_30, k1_relat_1(A_30), k2_relat_1(A_30)) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.32/1.96  tff(c_672, plain, (![A_127]: (v1_funct_2(k2_funct_1(A_127), k2_relat_1(A_127), k2_relat_1(k2_funct_1(A_127))) | ~v1_funct_1(k2_funct_1(A_127)) | ~v1_relat_1(k2_funct_1(A_127)) | ~v2_funct_1(A_127) | ~v1_funct_1(A_127) | ~v1_relat_1(A_127))), inference(superposition, [status(thm), theory('equality')], [c_427, c_48])).
% 5.32/1.96  tff(c_678, plain, (![A_7]: (v1_funct_2(k2_funct_1(A_7), k2_relat_1(A_7), k1_relat_1(A_7)) | ~v1_funct_1(k2_funct_1(A_7)) | ~v1_relat_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_12, c_672])).
% 5.32/1.96  tff(c_467, plain, (![A_97]: (m1_subset_1(A_97, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_97), k2_relat_1(A_97)))) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.32/1.96  tff(c_750, plain, (![A_135]: (m1_subset_1(k2_funct_1(A_135), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_135), k2_relat_1(k2_funct_1(A_135))))) | ~v1_funct_1(k2_funct_1(A_135)) | ~v1_relat_1(k2_funct_1(A_135)) | ~v2_funct_1(A_135) | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(superposition, [status(thm), theory('equality')], [c_14, c_467])).
% 5.32/1.96  tff(c_967, plain, (![A_146]: (m1_subset_1(k2_funct_1(A_146), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_146), k1_relat_1(A_146)))) | ~v1_funct_1(k2_funct_1(A_146)) | ~v1_relat_1(k2_funct_1(A_146)) | ~v2_funct_1(A_146) | ~v1_funct_1(A_146) | ~v1_relat_1(A_146) | ~v2_funct_1(A_146) | ~v1_funct_1(A_146) | ~v1_relat_1(A_146))), inference(superposition, [status(thm), theory('equality')], [c_12, c_750])).
% 5.32/1.96  tff(c_40, plain, (![B_26, A_25, C_27]: (k1_xboole_0=B_26 | k1_relset_1(A_25, B_26, C_27)=A_25 | ~v1_funct_2(C_27, A_25, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.32/1.96  tff(c_1084, plain, (![A_154]: (k1_relat_1(A_154)=k1_xboole_0 | k1_relset_1(k2_relat_1(A_154), k1_relat_1(A_154), k2_funct_1(A_154))=k2_relat_1(A_154) | ~v1_funct_2(k2_funct_1(A_154), k2_relat_1(A_154), k1_relat_1(A_154)) | ~v1_funct_1(k2_funct_1(A_154)) | ~v1_relat_1(k2_funct_1(A_154)) | ~v2_funct_1(A_154) | ~v1_funct_1(A_154) | ~v1_relat_1(A_154))), inference(resolution, [status(thm)], [c_967, c_40])).
% 5.32/1.96  tff(c_1095, plain, (![A_155]: (k1_relat_1(A_155)=k1_xboole_0 | k1_relset_1(k2_relat_1(A_155), k1_relat_1(A_155), k2_funct_1(A_155))=k2_relat_1(A_155) | ~v1_funct_1(k2_funct_1(A_155)) | ~v1_relat_1(k2_funct_1(A_155)) | ~v2_funct_1(A_155) | ~v1_funct_1(A_155) | ~v1_relat_1(A_155))), inference(resolution, [status(thm)], [c_678, c_1084])).
% 5.32/1.96  tff(c_166, plain, (![A_63, B_64, C_65]: (k2_relset_1(A_63, B_64, C_65)=k2_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.32/1.96  tff(c_170, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_105, c_166])).
% 5.32/1.96  tff(c_221, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_99])).
% 5.32/1.96  tff(c_235, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_221, c_54])).
% 5.32/1.96  tff(c_239, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_235])).
% 5.32/1.96  tff(c_240, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_239])).
% 5.32/1.96  tff(c_124, plain, (![C_54, A_55, B_56]: (v4_relat_1(C_54, A_55) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.32/1.96  tff(c_128, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_105, c_124])).
% 5.32/1.96  tff(c_131, plain, (![B_59, A_60]: (k1_relat_1(B_59)=A_60 | ~v1_partfun1(B_59, A_60) | ~v4_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.32/1.96  tff(c_134, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_128, c_131])).
% 5.32/1.96  tff(c_137, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_134])).
% 5.32/1.96  tff(c_138, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_137])).
% 5.32/1.96  tff(c_230, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_90])).
% 5.32/1.96  tff(c_229, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_105])).
% 5.32/1.96  tff(c_342, plain, (![C_89, A_90, B_91]: (v1_partfun1(C_89, A_90) | ~v1_funct_2(C_89, A_90, B_91) | ~v1_funct_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | v1_xboole_0(B_91))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.32/1.96  tff(c_345, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_229, c_342])).
% 5.32/1.96  tff(c_351, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_230, c_345])).
% 5.32/1.96  tff(c_353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_138, c_351])).
% 5.32/1.96  tff(c_354, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_137])).
% 5.32/1.96  tff(c_358, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_105])).
% 5.32/1.96  tff(c_442, plain, (![A_94, B_95, C_96]: (k2_relset_1(A_94, B_95, C_96)=k2_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.32/1.96  tff(c_446, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_358, c_442])).
% 5.32/1.96  tff(c_359, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_354, c_99])).
% 5.32/1.96  tff(c_447, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_446, c_359])).
% 5.32/1.96  tff(c_360, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_90])).
% 5.32/1.96  tff(c_454, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_447, c_360])).
% 5.32/1.96  tff(c_452, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_447, c_446])).
% 5.32/1.96  tff(c_453, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_447, c_358])).
% 5.32/1.96  tff(c_679, plain, (![A_128, B_129, C_130]: (k2_tops_2(A_128, B_129, C_130)=k2_funct_1(C_130) | ~v2_funct_1(C_130) | k2_relset_1(A_128, B_129, C_130)!=B_129 | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~v1_funct_2(C_130, A_128, B_129) | ~v1_funct_1(C_130))), inference(cnfTransformation, [status(thm)], [f_152])).
% 5.32/1.96  tff(c_682, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_453, c_679])).
% 5.32/1.96  tff(c_688, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_454, c_452, c_60, c_682])).
% 5.32/1.96  tff(c_58, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.32/1.96  tff(c_116, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_84, c_83, c_83, c_84, c_84, c_83, c_83, c_58])).
% 5.32/1.96  tff(c_117, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_116])).
% 5.32/1.96  tff(c_356, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_354, c_354, c_117])).
% 5.32/1.96  tff(c_591, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_447, c_447, c_447, c_356])).
% 5.32/1.96  tff(c_690, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_688, c_591])).
% 5.32/1.96  tff(c_1101, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1095, c_690])).
% 5.32/1.96  tff(c_1114, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_68, c_60, c_1101])).
% 5.32/1.96  tff(c_1116, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1114])).
% 5.32/1.96  tff(c_1119, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_1116])).
% 5.32/1.96  tff(c_1123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_68, c_1119])).
% 5.32/1.96  tff(c_1124, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1114])).
% 5.32/1.96  tff(c_1126, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1124])).
% 5.32/1.96  tff(c_1136, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_1126])).
% 5.32/1.96  tff(c_1140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_68, c_1136])).
% 5.32/1.96  tff(c_1141, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1124])).
% 5.32/1.96  tff(c_365, plain, (~v1_xboole_0(k1_relat_1('#skF_3')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_354, c_54])).
% 5.32/1.96  tff(c_369, plain, (~v1_xboole_0(k1_relat_1('#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_365])).
% 5.32/1.96  tff(c_401, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_369])).
% 5.32/1.96  tff(c_1149, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1141, c_401])).
% 5.32/1.96  tff(c_1156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1149])).
% 5.32/1.96  tff(c_1158, plain, (v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_369])).
% 5.32/1.96  tff(c_1258, plain, (![A_161]: (m1_subset_1(A_161, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_161), k2_relat_1(A_161)))) | ~v1_funct_1(A_161) | ~v1_relat_1(A_161))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.32/1.96  tff(c_20, plain, (![C_13, A_11, B_12]: (v4_relat_1(C_13, A_11) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.32/1.96  tff(c_1288, plain, (![A_163]: (v4_relat_1(A_163, k1_relat_1(A_163)) | ~v1_funct_1(A_163) | ~v1_relat_1(A_163))), inference(resolution, [status(thm)], [c_1258, c_20])).
% 5.32/1.96  tff(c_42, plain, (![B_29]: (v1_partfun1(B_29, k1_relat_1(B_29)) | ~v4_relat_1(B_29, k1_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.32/1.96  tff(c_1300, plain, (![A_163]: (v1_partfun1(A_163, k1_relat_1(A_163)) | ~v1_funct_1(A_163) | ~v1_relat_1(A_163))), inference(resolution, [status(thm)], [c_1288, c_42])).
% 5.32/1.96  tff(c_46, plain, (![A_30]: (m1_subset_1(A_30, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_30), k2_relat_1(A_30)))) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.32/1.96  tff(c_1337, plain, (![C_167, A_168, B_169]: (~v1_partfun1(C_167, A_168) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~v1_xboole_0(B_169) | v1_xboole_0(A_168))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.32/1.96  tff(c_1349, plain, (![A_172]: (~v1_partfun1(A_172, k1_relat_1(A_172)) | ~v1_xboole_0(k2_relat_1(A_172)) | v1_xboole_0(k1_relat_1(A_172)) | ~v1_funct_1(A_172) | ~v1_relat_1(A_172))), inference(resolution, [status(thm)], [c_46, c_1337])).
% 5.32/1.96  tff(c_1363, plain, (![A_173]: (~v1_xboole_0(k2_relat_1(A_173)) | v1_xboole_0(k1_relat_1(A_173)) | ~v1_funct_1(A_173) | ~v1_relat_1(A_173))), inference(resolution, [status(thm)], [c_1300, c_1349])).
% 5.32/1.96  tff(c_1440, plain, (![A_193]: (~v1_xboole_0(k1_relat_1(A_193)) | v1_xboole_0(k1_relat_1(k2_funct_1(A_193))) | ~v1_funct_1(k2_funct_1(A_193)) | ~v1_relat_1(k2_funct_1(A_193)) | ~v2_funct_1(A_193) | ~v1_funct_1(A_193) | ~v1_relat_1(A_193))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1363])).
% 5.32/1.96  tff(c_1646, plain, (![A_205]: (~v1_xboole_0(k1_relat_1(A_205)) | v1_xboole_0(k2_relat_1(A_205)) | ~v1_funct_1(k2_funct_1(A_205)) | ~v1_relat_1(k2_funct_1(A_205)) | ~v2_funct_1(A_205) | ~v1_funct_1(A_205) | ~v1_relat_1(A_205) | ~v2_funct_1(A_205) | ~v1_funct_1(A_205) | ~v1_relat_1(A_205))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1440])).
% 5.32/1.96  tff(c_1199, plain, (![A_158, B_159, C_160]: (k2_relset_1(A_158, B_159, C_160)=k2_relat_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.32/1.96  tff(c_1203, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_358, c_1199])).
% 5.32/1.96  tff(c_1204, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1203, c_359])).
% 5.32/1.96  tff(c_1217, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1204, c_54])).
% 5.32/1.96  tff(c_1221, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1217])).
% 5.32/1.96  tff(c_1222, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_72, c_1221])).
% 5.32/1.96  tff(c_1655, plain, (~v1_xboole_0(k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1646, c_1222])).
% 5.32/1.96  tff(c_1663, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_68, c_60, c_1158, c_1655])).
% 5.32/1.96  tff(c_1664, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1663])).
% 5.32/1.96  tff(c_1667, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_1664])).
% 5.32/1.96  tff(c_1671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_68, c_1667])).
% 5.32/1.96  tff(c_1672, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1663])).
% 5.32/1.96  tff(c_1693, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_1672])).
% 5.32/1.96  tff(c_1697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_68, c_1693])).
% 5.32/1.96  tff(c_1698, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_116])).
% 5.32/1.96  tff(c_1922, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1920, c_1920, c_1920, c_1698])).
% 5.32/1.96  tff(c_2160, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2057, c_2057, c_1922])).
% 5.32/1.96  tff(c_2237, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2234, c_2160])).
% 5.32/1.96  tff(c_2600, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2594, c_2237])).
% 5.32/1.96  tff(c_2612, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_68, c_60, c_2600])).
% 5.32/1.96  tff(c_2614, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2612])).
% 5.32/1.96  tff(c_2617, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_2614])).
% 5.32/1.96  tff(c_2621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_68, c_2617])).
% 5.32/1.96  tff(c_2622, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_2612])).
% 5.32/1.96  tff(c_2624, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_2622])).
% 5.32/1.96  tff(c_2627, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_2624])).
% 5.32/1.96  tff(c_2631, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_68, c_60, c_2627])).
% 5.32/1.96  tff(c_2632, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2622])).
% 5.32/1.96  tff(c_2636, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_2632])).
% 5.32/1.96  tff(c_2640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_68, c_2636])).
% 5.32/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.32/1.96  
% 5.32/1.96  Inference rules
% 5.32/1.96  ----------------------
% 5.32/1.96  #Ref     : 0
% 5.32/1.96  #Sup     : 596
% 5.32/1.96  #Fact    : 0
% 5.32/1.96  #Define  : 0
% 5.32/1.96  #Split   : 14
% 5.32/1.96  #Chain   : 0
% 5.32/1.96  #Close   : 0
% 5.32/1.96  
% 5.32/1.96  Ordering : KBO
% 5.32/1.96  
% 5.32/1.96  Simplification rules
% 5.32/1.96  ----------------------
% 5.32/1.96  #Subsume      : 107
% 5.32/1.96  #Demod        : 320
% 5.32/1.96  #Tautology    : 234
% 5.32/1.96  #SimpNegUnit  : 15
% 5.32/1.96  #BackRed      : 64
% 5.32/1.96  
% 5.32/1.96  #Partial instantiations: 0
% 5.32/1.96  #Strategies tried      : 1
% 5.32/1.96  
% 5.32/1.96  Timing (in seconds)
% 5.32/1.96  ----------------------
% 5.32/1.97  Preprocessing        : 0.38
% 5.32/1.97  Parsing              : 0.20
% 5.32/1.97  CNF conversion       : 0.02
% 5.32/1.97  Main loop            : 0.77
% 5.32/1.97  Inferencing          : 0.29
% 5.32/1.97  Reduction            : 0.25
% 5.32/1.97  Demodulation         : 0.17
% 5.32/1.97  BG Simplification    : 0.04
% 5.32/1.97  Subsumption          : 0.12
% 5.32/1.97  Abstraction          : 0.04
% 5.32/1.97  MUC search           : 0.00
% 5.32/1.97  Cooper               : 0.00
% 5.32/1.97  Total                : 1.21
% 5.32/1.97  Index Insertion      : 0.00
% 5.32/1.97  Index Deletion       : 0.00
% 5.32/1.97  Index Matching       : 0.00
% 5.32/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
