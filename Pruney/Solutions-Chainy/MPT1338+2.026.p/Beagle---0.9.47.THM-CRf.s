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
% DateTime   : Thu Dec  3 10:23:17 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  178 (4845 expanded)
%              Number of leaves         :   47 (1707 expanded)
%              Depth                    :   22
%              Number of atoms          :  297 (14728 expanded)
%              Number of equality atoms :   93 (4822 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_120,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_140,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_152,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_91,axiom,(
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

tff(c_76,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_106,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_114,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_106])).

tff(c_72,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_113,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_106])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_160,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_113,c_66])).

tff(c_20,plain,(
    ! [C_11,A_9,B_10] :
      ( v1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_164,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_160,c_20])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_62,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_16,plain,(
    ! [A_8] :
      ( k2_relat_1(k2_funct_1(A_8)) = k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_6] :
      ( v1_xboole_0(k2_relat_1(A_6))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1012,plain,(
    ! [A_169,B_170,C_171] :
      ( k2_relset_1(A_169,B_170,C_171) = k2_relat_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1022,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_160,c_1012])).

tff(c_64,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_143,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_113,c_64])).

tff(c_1023,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1022,c_143])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_125,plain,(
    ! [A_43] :
      ( ~ v1_xboole_0(u1_struct_0(A_43))
      | ~ l1_struct_0(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_131,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_125])).

tff(c_135,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_131])).

tff(c_136,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_135])).

tff(c_1032,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_136])).

tff(c_1042,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_1032])).

tff(c_8,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_960,plain,(
    ! [C_159,A_160,B_161] :
      ( v4_relat_1(C_159,A_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_970,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_160,c_960])).

tff(c_974,plain,(
    ! [B_165,A_166] :
      ( k1_relat_1(B_165) = A_166
      | ~ v1_partfun1(B_165,A_166)
      | ~ v4_relat_1(B_165,A_166)
      | ~ v1_relat_1(B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_977,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_970,c_974])).

tff(c_980,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_977])).

tff(c_981,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_980])).

tff(c_68,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_115,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_68])).

tff(c_124,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_115])).

tff(c_1033,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_124])).

tff(c_1031,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_160])).

tff(c_1089,plain,(
    ! [B_185,C_186,A_187] :
      ( k1_xboole_0 = B_185
      | v1_partfun1(C_186,A_187)
      | ~ v1_funct_2(C_186,A_187,B_185)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_187,B_185)))
      | ~ v1_funct_1(C_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1092,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1031,c_1089])).

tff(c_1101,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1033,c_1092])).

tff(c_1102,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_981,c_1101])).

tff(c_14,plain,(
    ! [A_7] :
      ( r1_tarski(A_7,k2_zfmisc_1(k1_relat_1(A_7),k2_relat_1(A_7)))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1116,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),k1_xboole_0))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1102,c_14])).

tff(c_1123,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_8,c_1116])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_165,plain,(
    ! [B_50,A_51] :
      ( ~ r1_xboole_0(B_50,A_51)
      | ~ r1_tarski(B_50,A_51)
      | v1_xboole_0(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_169,plain,(
    ! [A_1] :
      ( ~ r1_tarski(A_1,k1_xboole_0)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_165])).

tff(c_1141,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1123,c_169])).

tff(c_1145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1042,c_1141])).

tff(c_1146,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_980])).

tff(c_1150,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1146,c_160])).

tff(c_1231,plain,(
    ! [A_190,B_191,C_192] :
      ( k2_relset_1(A_190,B_191,C_192) = k2_relat_1(C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1241,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1150,c_1231])).

tff(c_1151,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1146,c_143])).

tff(c_1242,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1241,c_1151])).

tff(c_1153,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1146,c_124])).

tff(c_1249,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_1153])).

tff(c_1248,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_1150])).

tff(c_1247,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_1241])).

tff(c_1472,plain,(
    ! [A_238,B_239,C_240] :
      ( k2_tops_2(A_238,B_239,C_240) = k2_funct_1(C_240)
      | ~ v2_funct_1(C_240)
      | k2_relset_1(A_238,B_239,C_240) != B_239
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239)))
      | ~ v1_funct_2(C_240,A_238,B_239)
      | ~ v1_funct_1(C_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1478,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1248,c_1472])).

tff(c_1488,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1249,c_1247,c_62,c_1478])).

tff(c_54,plain,(
    ! [A_31,B_32,C_33] :
      ( m1_subset_1(k2_tops_2(A_31,B_32,C_33),k1_zfmisc_1(k2_zfmisc_1(B_32,A_31)))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_2(C_33,A_31,B_32)
      | ~ v1_funct_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1497,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1488,c_54])).

tff(c_1501,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1249,c_1248,c_1497])).

tff(c_26,plain,(
    ! [A_15,B_16,C_17] :
      ( k2_relset_1(A_15,B_16,C_17) = k2_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1589,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1501,c_26])).

tff(c_239,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_249,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_160,c_239])).

tff(c_250,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_143])).

tff(c_259,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_136])).

tff(c_269,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_259])).

tff(c_187,plain,(
    ! [C_60,A_61,B_62] :
      ( v4_relat_1(C_60,A_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_197,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_160,c_187])).

tff(c_231,plain,(
    ! [B_68,A_69] :
      ( k1_relat_1(B_68) = A_69
      | ~ v1_partfun1(B_68,A_69)
      | ~ v4_relat_1(B_68,A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_234,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_197,c_231])).

tff(c_237,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_234])).

tff(c_238,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_237])).

tff(c_260,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_124])).

tff(c_258,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_160])).

tff(c_344,plain,(
    ! [B_92,C_93,A_94] :
      ( k1_xboole_0 = B_92
      | v1_partfun1(C_93,A_94)
      | ~ v1_funct_2(C_93,A_94,B_92)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_92)))
      | ~ v1_funct_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_347,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_258,c_344])).

tff(c_356,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_260,c_347])).

tff(c_357,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_356])).

tff(c_372,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),k1_xboole_0))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_14])).

tff(c_379,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_8,c_372])).

tff(c_404,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_379,c_169])).

tff(c_408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_404])).

tff(c_409,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_413,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_160])).

tff(c_466,plain,(
    ! [A_100,B_101,C_102] :
      ( k2_relset_1(A_100,B_101,C_102) = k2_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_476,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_413,c_466])).

tff(c_414,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_143])).

tff(c_477,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_414])).

tff(c_486,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_136])).

tff(c_495,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_486])).

tff(c_10,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_416,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_124])).

tff(c_484,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_416])).

tff(c_482,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_476])).

tff(c_483,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_413])).

tff(c_735,plain,(
    ! [A_150,B_151,C_152] :
      ( k2_tops_2(A_150,B_151,C_152) = k2_funct_1(C_152)
      | ~ v2_funct_1(C_152)
      | k2_relset_1(A_150,B_151,C_152) != B_151
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151)))
      | ~ v1_funct_2(C_152,A_150,B_151)
      | ~ v1_funct_1(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_741,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_483,c_735])).

tff(c_751,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_484,c_482,c_62,c_741])).

tff(c_60,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_182,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_114,c_113,c_113,c_114,c_114,c_113,c_113,c_60])).

tff(c_183,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_411,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_409,c_183])).

tff(c_531,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_477,c_477,c_411])).

tff(c_755,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_531])).

tff(c_606,plain,(
    ! [A_131,B_132,C_133] :
      ( v1_funct_2(k2_tops_2(A_131,B_132,C_133),B_132,A_131)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_2(C_133,A_131,B_132)
      | ~ v1_funct_1(C_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_608,plain,
    ( v1_funct_2(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_483,c_606])).

tff(c_615,plain,(
    v1_funct_2(k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_484,c_608])).

tff(c_753,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_615])).

tff(c_759,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_751,c_54])).

tff(c_763,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_484,c_483,c_759])).

tff(c_38,plain,(
    ! [B_19,A_18,C_20] :
      ( k1_xboole_0 = B_19
      | k1_relset_1(A_18,B_19,C_20) = A_18
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_784,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_763,c_38])).

tff(c_816,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_784])).

tff(c_817,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_755,c_816])).

tff(c_847,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_3')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_817,c_14])).

tff(c_855,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_10,c_847])).

tff(c_950,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_855,c_169])).

tff(c_954,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_495,c_950])).

tff(c_955,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_1148,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1146,c_1146,c_1146,c_955])).

tff(c_1306,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1242,c_1242,c_1148])).

tff(c_1492,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1488,c_1306])).

tff(c_1601,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1589,c_1492])).

tff(c_1637,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1601])).

tff(c_1641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_70,c_62,c_1637])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:49:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.08/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.72  
% 4.08/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.72  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.08/1.72  
% 4.08/1.72  %Foreground sorts:
% 4.08/1.72  
% 4.08/1.72  
% 4.08/1.72  %Background operators:
% 4.08/1.72  
% 4.08/1.72  
% 4.08/1.72  %Foreground operators:
% 4.08/1.72  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.08/1.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.08/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.08/1.72  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.08/1.72  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.08/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.08/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.08/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.08/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.08/1.72  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.08/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.08/1.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.08/1.72  tff('#skF_2', type, '#skF_2': $i).
% 4.08/1.72  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.08/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.08/1.72  tff('#skF_1', type, '#skF_1': $i).
% 4.08/1.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.08/1.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.08/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.08/1.72  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.08/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.08/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.08/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.08/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.08/1.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.08/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.08/1.72  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.08/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.08/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.08/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.08/1.72  
% 4.08/1.74  tff(f_176, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 4.08/1.74  tff(f_120, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.08/1.74  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.08/1.74  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.08/1.74  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 4.08/1.74  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.08/1.74  tff(f_128, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.08/1.74  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.08/1.74  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.08/1.74  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 4.08/1.74  tff(f_116, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 4.08/1.74  tff(f_49, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 4.08/1.74  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.08/1.74  tff(f_35, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.08/1.74  tff(f_140, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 4.08/1.74  tff(f_152, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 4.08/1.74  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.08/1.74  tff(c_76, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.08/1.74  tff(c_106, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.08/1.74  tff(c_114, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_76, c_106])).
% 4.08/1.74  tff(c_72, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.08/1.74  tff(c_113, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_106])).
% 4.08/1.74  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.08/1.74  tff(c_160, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_113, c_66])).
% 4.08/1.74  tff(c_20, plain, (![C_11, A_9, B_10]: (v1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.08/1.74  tff(c_164, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_160, c_20])).
% 4.08/1.74  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.08/1.74  tff(c_62, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.08/1.74  tff(c_16, plain, (![A_8]: (k2_relat_1(k2_funct_1(A_8))=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.08/1.74  tff(c_12, plain, (![A_6]: (v1_xboole_0(k2_relat_1(A_6)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.08/1.74  tff(c_1012, plain, (![A_169, B_170, C_171]: (k2_relset_1(A_169, B_170, C_171)=k2_relat_1(C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.08/1.74  tff(c_1022, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_160, c_1012])).
% 4.08/1.74  tff(c_64, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.08/1.74  tff(c_143, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_113, c_64])).
% 4.08/1.74  tff(c_1023, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1022, c_143])).
% 4.08/1.74  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.08/1.74  tff(c_125, plain, (![A_43]: (~v1_xboole_0(u1_struct_0(A_43)) | ~l1_struct_0(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.08/1.74  tff(c_131, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_113, c_125])).
% 4.08/1.74  tff(c_135, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_131])).
% 4.08/1.74  tff(c_136, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_74, c_135])).
% 4.08/1.74  tff(c_1032, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1023, c_136])).
% 4.08/1.74  tff(c_1042, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_1032])).
% 4.08/1.74  tff(c_8, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.08/1.74  tff(c_960, plain, (![C_159, A_160, B_161]: (v4_relat_1(C_159, A_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.08/1.74  tff(c_970, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_160, c_960])).
% 4.08/1.74  tff(c_974, plain, (![B_165, A_166]: (k1_relat_1(B_165)=A_166 | ~v1_partfun1(B_165, A_166) | ~v4_relat_1(B_165, A_166) | ~v1_relat_1(B_165))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.08/1.74  tff(c_977, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_970, c_974])).
% 4.08/1.74  tff(c_980, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_977])).
% 4.08/1.74  tff(c_981, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_980])).
% 4.08/1.74  tff(c_68, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.08/1.74  tff(c_115, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_68])).
% 4.08/1.74  tff(c_124, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_115])).
% 4.08/1.74  tff(c_1033, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1023, c_124])).
% 4.08/1.74  tff(c_1031, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1023, c_160])).
% 4.08/1.74  tff(c_1089, plain, (![B_185, C_186, A_187]: (k1_xboole_0=B_185 | v1_partfun1(C_186, A_187) | ~v1_funct_2(C_186, A_187, B_185) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_187, B_185))) | ~v1_funct_1(C_186))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.08/1.74  tff(c_1092, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1031, c_1089])).
% 4.08/1.74  tff(c_1101, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1033, c_1092])).
% 4.08/1.74  tff(c_1102, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_981, c_1101])).
% 4.08/1.74  tff(c_14, plain, (![A_7]: (r1_tarski(A_7, k2_zfmisc_1(k1_relat_1(A_7), k2_relat_1(A_7))) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.08/1.74  tff(c_1116, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), k1_xboole_0)) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1102, c_14])).
% 4.08/1.74  tff(c_1123, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_164, c_8, c_1116])).
% 4.08/1.74  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.08/1.74  tff(c_165, plain, (![B_50, A_51]: (~r1_xboole_0(B_50, A_51) | ~r1_tarski(B_50, A_51) | v1_xboole_0(B_50))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.08/1.74  tff(c_169, plain, (![A_1]: (~r1_tarski(A_1, k1_xboole_0) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_2, c_165])).
% 4.08/1.74  tff(c_1141, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1123, c_169])).
% 4.08/1.74  tff(c_1145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1042, c_1141])).
% 4.08/1.74  tff(c_1146, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_980])).
% 4.08/1.74  tff(c_1150, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1146, c_160])).
% 4.08/1.74  tff(c_1231, plain, (![A_190, B_191, C_192]: (k2_relset_1(A_190, B_191, C_192)=k2_relat_1(C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.08/1.74  tff(c_1241, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1150, c_1231])).
% 4.08/1.74  tff(c_1151, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1146, c_143])).
% 4.08/1.74  tff(c_1242, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1241, c_1151])).
% 4.08/1.74  tff(c_1153, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1146, c_124])).
% 4.08/1.74  tff(c_1249, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1242, c_1153])).
% 4.08/1.74  tff(c_1248, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1242, c_1150])).
% 4.08/1.74  tff(c_1247, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1242, c_1241])).
% 4.08/1.74  tff(c_1472, plain, (![A_238, B_239, C_240]: (k2_tops_2(A_238, B_239, C_240)=k2_funct_1(C_240) | ~v2_funct_1(C_240) | k2_relset_1(A_238, B_239, C_240)!=B_239 | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))) | ~v1_funct_2(C_240, A_238, B_239) | ~v1_funct_1(C_240))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.08/1.74  tff(c_1478, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1248, c_1472])).
% 4.08/1.74  tff(c_1488, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1249, c_1247, c_62, c_1478])).
% 4.08/1.74  tff(c_54, plain, (![A_31, B_32, C_33]: (m1_subset_1(k2_tops_2(A_31, B_32, C_33), k1_zfmisc_1(k2_zfmisc_1(B_32, A_31))) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_2(C_33, A_31, B_32) | ~v1_funct_1(C_33))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.08/1.74  tff(c_1497, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1488, c_54])).
% 4.08/1.74  tff(c_1501, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1249, c_1248, c_1497])).
% 4.08/1.74  tff(c_26, plain, (![A_15, B_16, C_17]: (k2_relset_1(A_15, B_16, C_17)=k2_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.08/1.74  tff(c_1589, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1501, c_26])).
% 4.08/1.74  tff(c_239, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.08/1.74  tff(c_249, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_160, c_239])).
% 4.08/1.74  tff(c_250, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_143])).
% 4.08/1.74  tff(c_259, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_136])).
% 4.08/1.74  tff(c_269, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_259])).
% 4.08/1.74  tff(c_187, plain, (![C_60, A_61, B_62]: (v4_relat_1(C_60, A_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.08/1.74  tff(c_197, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_160, c_187])).
% 4.08/1.74  tff(c_231, plain, (![B_68, A_69]: (k1_relat_1(B_68)=A_69 | ~v1_partfun1(B_68, A_69) | ~v4_relat_1(B_68, A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.08/1.74  tff(c_234, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_197, c_231])).
% 4.08/1.74  tff(c_237, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_234])).
% 4.08/1.74  tff(c_238, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_237])).
% 4.08/1.74  tff(c_260, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_124])).
% 4.08/1.74  tff(c_258, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_160])).
% 4.08/1.74  tff(c_344, plain, (![B_92, C_93, A_94]: (k1_xboole_0=B_92 | v1_partfun1(C_93, A_94) | ~v1_funct_2(C_93, A_94, B_92) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_92))) | ~v1_funct_1(C_93))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.08/1.74  tff(c_347, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_258, c_344])).
% 4.08/1.74  tff(c_356, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_260, c_347])).
% 4.08/1.74  tff(c_357, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_238, c_356])).
% 4.08/1.74  tff(c_372, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), k1_xboole_0)) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_357, c_14])).
% 4.08/1.74  tff(c_379, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_164, c_8, c_372])).
% 4.08/1.74  tff(c_404, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_379, c_169])).
% 4.08/1.74  tff(c_408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_269, c_404])).
% 4.08/1.74  tff(c_409, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_237])).
% 4.08/1.74  tff(c_413, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_409, c_160])).
% 4.08/1.74  tff(c_466, plain, (![A_100, B_101, C_102]: (k2_relset_1(A_100, B_101, C_102)=k2_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.08/1.74  tff(c_476, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_413, c_466])).
% 4.08/1.74  tff(c_414, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_409, c_143])).
% 4.08/1.74  tff(c_477, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_476, c_414])).
% 4.08/1.74  tff(c_486, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_136])).
% 4.08/1.74  tff(c_495, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_486])).
% 4.08/1.74  tff(c_10, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.08/1.74  tff(c_416, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_409, c_124])).
% 4.08/1.74  tff(c_484, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_416])).
% 4.08/1.74  tff(c_482, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_477, c_476])).
% 4.08/1.74  tff(c_483, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_413])).
% 4.08/1.74  tff(c_735, plain, (![A_150, B_151, C_152]: (k2_tops_2(A_150, B_151, C_152)=k2_funct_1(C_152) | ~v2_funct_1(C_152) | k2_relset_1(A_150, B_151, C_152)!=B_151 | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))) | ~v1_funct_2(C_152, A_150, B_151) | ~v1_funct_1(C_152))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.08/1.74  tff(c_741, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_483, c_735])).
% 4.08/1.74  tff(c_751, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_484, c_482, c_62, c_741])).
% 4.08/1.74  tff(c_60, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.08/1.74  tff(c_182, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_114, c_113, c_113, c_114, c_114, c_113, c_113, c_60])).
% 4.08/1.74  tff(c_183, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_182])).
% 4.08/1.74  tff(c_411, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_409, c_409, c_183])).
% 4.08/1.74  tff(c_531, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_477, c_477, c_477, c_411])).
% 4.08/1.74  tff(c_755, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_751, c_531])).
% 4.08/1.74  tff(c_606, plain, (![A_131, B_132, C_133]: (v1_funct_2(k2_tops_2(A_131, B_132, C_133), B_132, A_131) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_2(C_133, A_131, B_132) | ~v1_funct_1(C_133))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.08/1.74  tff(c_608, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_483, c_606])).
% 4.08/1.74  tff(c_615, plain, (v1_funct_2(k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_484, c_608])).
% 4.08/1.74  tff(c_753, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_751, c_615])).
% 4.08/1.74  tff(c_759, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_751, c_54])).
% 4.08/1.74  tff(c_763, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_484, c_483, c_759])).
% 4.08/1.74  tff(c_38, plain, (![B_19, A_18, C_20]: (k1_xboole_0=B_19 | k1_relset_1(A_18, B_19, C_20)=A_18 | ~v1_funct_2(C_20, A_18, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.08/1.74  tff(c_784, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_763, c_38])).
% 4.08/1.74  tff(c_816, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_753, c_784])).
% 4.08/1.74  tff(c_817, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_755, c_816])).
% 4.08/1.74  tff(c_847, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_3'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_817, c_14])).
% 4.08/1.74  tff(c_855, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_164, c_10, c_847])).
% 4.08/1.74  tff(c_950, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_855, c_169])).
% 4.08/1.74  tff(c_954, plain, $false, inference(negUnitSimplification, [status(thm)], [c_495, c_950])).
% 4.08/1.74  tff(c_955, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_182])).
% 4.08/1.74  tff(c_1148, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1146, c_1146, c_1146, c_955])).
% 4.08/1.74  tff(c_1306, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1242, c_1242, c_1148])).
% 4.08/1.74  tff(c_1492, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1488, c_1306])).
% 4.08/1.74  tff(c_1601, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1589, c_1492])).
% 4.08/1.74  tff(c_1637, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_1601])).
% 4.08/1.74  tff(c_1641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_70, c_62, c_1637])).
% 4.08/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.74  
% 4.08/1.74  Inference rules
% 4.08/1.74  ----------------------
% 4.08/1.74  #Ref     : 0
% 4.08/1.74  #Sup     : 371
% 4.08/1.75  #Fact    : 0
% 4.08/1.75  #Define  : 0
% 4.08/1.75  #Split   : 10
% 4.08/1.75  #Chain   : 0
% 4.08/1.75  #Close   : 0
% 4.08/1.75  
% 4.08/1.75  Ordering : KBO
% 4.08/1.75  
% 4.08/1.75  Simplification rules
% 4.08/1.75  ----------------------
% 4.08/1.75  #Subsume      : 33
% 4.08/1.75  #Demod        : 278
% 4.08/1.75  #Tautology    : 155
% 4.08/1.75  #SimpNegUnit  : 13
% 4.08/1.75  #BackRed      : 85
% 4.08/1.75  
% 4.08/1.75  #Partial instantiations: 0
% 4.08/1.75  #Strategies tried      : 1
% 4.08/1.75  
% 4.08/1.75  Timing (in seconds)
% 4.08/1.75  ----------------------
% 4.41/1.75  Preprocessing        : 0.36
% 4.41/1.75  Parsing              : 0.19
% 4.41/1.75  CNF conversion       : 0.02
% 4.41/1.75  Main loop            : 0.55
% 4.41/1.75  Inferencing          : 0.19
% 4.41/1.75  Reduction            : 0.19
% 4.41/1.75  Demodulation         : 0.13
% 4.41/1.75  BG Simplification    : 0.03
% 4.41/1.75  Subsumption          : 0.10
% 4.41/1.75  Abstraction          : 0.03
% 4.41/1.75  MUC search           : 0.00
% 4.41/1.75  Cooper               : 0.00
% 4.41/1.75  Total                : 0.98
% 4.41/1.75  Index Insertion      : 0.00
% 4.41/1.75  Index Deletion       : 0.00
% 4.41/1.75  Index Matching       : 0.00
% 4.41/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
