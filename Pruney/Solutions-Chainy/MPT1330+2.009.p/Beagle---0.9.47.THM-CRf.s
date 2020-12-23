%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:10 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 861 expanded)
%              Number of leaves         :   42 ( 294 expanded)
%              Depth                    :   12
%              Number of atoms          :  193 (2285 expanded)
%              Number of equality atoms :   54 ( 883 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_132,negated_conjecture,(
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

tff(f_113,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_42,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k2_struct_0('#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_55,plain,(
    k2_struct_0('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_52,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_56,plain,(
    ! [A_56] :
      ( u1_struct_0(A_56) = k2_struct_0(A_56)
      | ~ l1_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_64,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_56])).

tff(c_50,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_63,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_56])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_65,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_44])).

tff(c_89,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_65])).

tff(c_14,plain,(
    ! [C_11,A_9,B_10] :
      ( v1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_96,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_89,c_14])).

tff(c_153,plain,(
    ! [C_83,A_84,B_85] :
      ( v4_relat_1(C_83,A_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_161,plain,(
    v4_relat_1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_89,c_153])).

tff(c_189,plain,(
    ! [B_97,A_98] :
      ( k1_relat_1(B_97) = A_98
      | ~ v1_partfun1(B_97,A_98)
      | ~ v4_relat_1(B_97,A_98)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_192,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_161,c_189])).

tff(c_195,plain,
    ( k2_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_192])).

tff(c_196,plain,(
    ~ v1_partfun1('#skF_4',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_46,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_66,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_46])).

tff(c_75,plain,(
    v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66])).

tff(c_263,plain,(
    ! [C_123,A_124,B_125] :
      ( v1_partfun1(C_123,A_124)
      | ~ v1_funct_2(C_123,A_124,B_125)
      | ~ v1_funct_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | v1_xboole_0(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_266,plain,
    ( v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',k2_struct_0('#skF_2'),k2_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_89,c_263])).

tff(c_273,plain,
    ( v1_partfun1('#skF_4',k2_struct_0('#skF_2'))
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_75,c_266])).

tff(c_274,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_273])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_278,plain,(
    k2_struct_0('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_274,c_2])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_278])).

tff(c_283,plain,(
    k2_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_40,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_98,plain,(
    k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_40])).

tff(c_289,plain,(
    k8_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_283,c_98])).

tff(c_290,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_89])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] :
      ( k1_relset_1(A_15,B_16,C_17) = k1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_364,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_290,c_20])).

tff(c_407,plain,(
    ! [A_144,B_145,C_146] :
      ( k8_relset_1(A_144,B_145,C_146,B_145) = k1_relset_1(A_144,B_145,C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_409,plain,(
    k8_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) = k1_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_290,c_407])).

tff(c_414,plain,(
    k8_relset_1(k1_relat_1('#skF_4'),k2_struct_0('#skF_3'),'#skF_4',k2_struct_0('#skF_3')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_409])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_414])).

tff(c_417,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_427,plain,(
    ! [A_147] :
      ( u1_struct_0(A_147) = k2_struct_0(A_147)
      | ~ l1_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_433,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_427])).

tff(c_437,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_433])).

tff(c_418,plain,(
    k2_struct_0('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_430,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_427])).

tff(c_435,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_430])).

tff(c_470,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_435,c_418,c_417,c_40])).

tff(c_438,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_44])).

tff(c_461,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_438])).

tff(c_468,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_461,c_14])).

tff(c_478,plain,(
    ! [C_160,A_161,B_162] :
      ( v4_relat_1(C_160,A_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_486,plain,(
    v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_461,c_478])).

tff(c_552,plain,(
    ! [B_183,A_184] :
      ( k1_relat_1(B_183) = A_184
      | ~ v1_partfun1(B_183,A_184)
      | ~ v4_relat_1(B_183,A_184)
      | ~ v1_relat_1(B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_555,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_partfun1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_486,c_552])).

tff(c_558,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_partfun1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_555])).

tff(c_559,plain,(
    ~ v1_partfun1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_558])).

tff(c_527,plain,(
    ! [B_180,A_181] :
      ( r1_tarski(k1_relat_1(B_180),A_181)
      | ~ v4_relat_1(B_180,A_181)
      | ~ v1_relat_1(B_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_1'(A_21),A_21)
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_494,plain,(
    ! [C_166,B_167,A_168] :
      ( ~ v1_xboole_0(C_166)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(C_166))
      | ~ r2_hidden(A_168,B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_502,plain,(
    ! [B_169,A_170,A_171] :
      ( ~ v1_xboole_0(B_169)
      | ~ r2_hidden(A_170,A_171)
      | ~ r1_tarski(A_171,B_169) ) ),
    inference(resolution,[status(thm)],[c_6,c_494])).

tff(c_505,plain,(
    ! [B_169,A_21] :
      ( ~ v1_xboole_0(B_169)
      | ~ r1_tarski(A_21,B_169)
      | k1_xboole_0 = A_21 ) ),
    inference(resolution,[status(thm)],[c_28,c_502])).

tff(c_575,plain,(
    ! [A_191,B_192] :
      ( ~ v1_xboole_0(A_191)
      | k1_relat_1(B_192) = k1_xboole_0
      | ~ v4_relat_1(B_192,A_191)
      | ~ v1_relat_1(B_192) ) ),
    inference(resolution,[status(thm)],[c_527,c_505])).

tff(c_578,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_486,c_575])).

tff(c_581,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_578])).

tff(c_582,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_581])).

tff(c_439,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_46])).

tff(c_448,plain,(
    v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_439])).

tff(c_641,plain,(
    ! [C_217,A_218,B_219] :
      ( v1_partfun1(C_217,A_218)
      | ~ v1_funct_2(C_217,A_218,B_219)
      | ~ v1_funct_1(C_217)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219)))
      | v1_xboole_0(B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_644,plain,
    ( v1_partfun1('#skF_4',k1_xboole_0)
    | ~ v1_funct_2('#skF_4',k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_461,c_641])).

tff(c_651,plain,
    ( v1_partfun1('#skF_4',k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_448,c_644])).

tff(c_653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_559,c_651])).

tff(c_654,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_581])).

tff(c_34,plain,(
    ! [B_48] :
      ( v1_partfun1(B_48,k1_relat_1(B_48))
      | ~ v4_relat_1(B_48,k1_relat_1(B_48))
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_665,plain,
    ( v1_partfun1('#skF_4',k1_relat_1('#skF_4'))
    | ~ v4_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_34])).

tff(c_675,plain,(
    v1_partfun1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_486,c_654,c_665])).

tff(c_677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_559,c_675])).

tff(c_678,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_558])).

tff(c_735,plain,(
    ! [A_223,B_224,C_225] :
      ( k1_relset_1(A_223,B_224,C_225) = k1_relat_1(C_225)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_738,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_461,c_735])).

tff(c_744,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_738])).

tff(c_771,plain,(
    ! [A_231,B_232,C_233] :
      ( k8_relset_1(A_231,B_232,C_233,B_232) = k1_relset_1(A_231,B_232,C_233)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_773,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4',k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_461,c_771])).

tff(c_778,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_744,c_773])).

tff(c_780,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_470,c_778])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.39  
% 2.84/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.39  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.84/1.39  
% 2.84/1.39  %Foreground sorts:
% 2.84/1.39  
% 2.84/1.39  
% 2.84/1.39  %Background operators:
% 2.84/1.39  
% 2.84/1.39  
% 2.84/1.39  %Foreground operators:
% 2.84/1.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.84/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.84/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.39  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.84/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.84/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.39  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.84/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.84/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.84/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.39  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.84/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.84/1.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.84/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.84/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.84/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.84/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.84/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.84/1.39  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.84/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.84/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.84/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.39  
% 2.84/1.41  tff(f_132, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 2.84/1.41  tff(f_113, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.84/1.41  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.84/1.41  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.84/1.41  tff(f_109, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.84/1.41  tff(f_101, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.84/1.41  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.84/1.41  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.84/1.41  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.84/1.41  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.84/1.41  tff(f_87, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.84/1.41  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.84/1.41  tff(f_40, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.84/1.41  tff(c_42, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k2_struct_0('#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.84/1.41  tff(c_55, plain, (k2_struct_0('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 2.84/1.41  tff(c_52, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.84/1.41  tff(c_56, plain, (![A_56]: (u1_struct_0(A_56)=k2_struct_0(A_56) | ~l1_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.84/1.41  tff(c_64, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_56])).
% 2.84/1.41  tff(c_50, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.84/1.41  tff(c_63, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_56])).
% 2.84/1.41  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.84/1.41  tff(c_65, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_44])).
% 2.84/1.41  tff(c_89, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_65])).
% 2.84/1.41  tff(c_14, plain, (![C_11, A_9, B_10]: (v1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.84/1.41  tff(c_96, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_89, c_14])).
% 2.84/1.41  tff(c_153, plain, (![C_83, A_84, B_85]: (v4_relat_1(C_83, A_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.84/1.41  tff(c_161, plain, (v4_relat_1('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_89, c_153])).
% 2.84/1.41  tff(c_189, plain, (![B_97, A_98]: (k1_relat_1(B_97)=A_98 | ~v1_partfun1(B_97, A_98) | ~v4_relat_1(B_97, A_98) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.84/1.41  tff(c_192, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_161, c_189])).
% 2.84/1.41  tff(c_195, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_192])).
% 2.84/1.41  tff(c_196, plain, (~v1_partfun1('#skF_4', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_195])).
% 2.84/1.41  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.84/1.41  tff(c_46, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.84/1.41  tff(c_66, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_46])).
% 2.84/1.41  tff(c_75, plain, (v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66])).
% 2.84/1.41  tff(c_263, plain, (![C_123, A_124, B_125]: (v1_partfun1(C_123, A_124) | ~v1_funct_2(C_123, A_124, B_125) | ~v1_funct_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | v1_xboole_0(B_125))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.84/1.41  tff(c_266, plain, (v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', k2_struct_0('#skF_2'), k2_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_89, c_263])).
% 2.84/1.41  tff(c_273, plain, (v1_partfun1('#skF_4', k2_struct_0('#skF_2')) | v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_75, c_266])).
% 2.84/1.41  tff(c_274, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_196, c_273])).
% 2.84/1.41  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.84/1.41  tff(c_278, plain, (k2_struct_0('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_274, c_2])).
% 2.84/1.41  tff(c_282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_278])).
% 2.84/1.41  tff(c_283, plain, (k2_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_195])).
% 2.84/1.41  tff(c_40, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.84/1.41  tff(c_98, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_40])).
% 2.84/1.41  tff(c_289, plain, (k8_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_283, c_98])).
% 2.84/1.41  tff(c_290, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_283, c_89])).
% 2.84/1.41  tff(c_20, plain, (![A_15, B_16, C_17]: (k1_relset_1(A_15, B_16, C_17)=k1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.84/1.41  tff(c_364, plain, (k1_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_290, c_20])).
% 2.84/1.41  tff(c_407, plain, (![A_144, B_145, C_146]: (k8_relset_1(A_144, B_145, C_146, B_145)=k1_relset_1(A_144, B_145, C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.84/1.41  tff(c_409, plain, (k8_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))=k1_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_290, c_407])).
% 2.84/1.41  tff(c_414, plain, (k8_relset_1(k1_relat_1('#skF_4'), k2_struct_0('#skF_3'), '#skF_4', k2_struct_0('#skF_3'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_364, c_409])).
% 2.84/1.41  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_289, c_414])).
% 2.84/1.41  tff(c_417, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.84/1.41  tff(c_427, plain, (![A_147]: (u1_struct_0(A_147)=k2_struct_0(A_147) | ~l1_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.84/1.41  tff(c_433, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_427])).
% 2.84/1.41  tff(c_437, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_417, c_433])).
% 2.84/1.41  tff(c_418, plain, (k2_struct_0('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.84/1.41  tff(c_430, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_427])).
% 2.84/1.41  tff(c_435, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_418, c_430])).
% 2.84/1.41  tff(c_470, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_437, c_435, c_418, c_417, c_40])).
% 2.84/1.41  tff(c_438, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_44])).
% 2.84/1.41  tff(c_461, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_437, c_438])).
% 2.84/1.41  tff(c_468, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_461, c_14])).
% 2.84/1.41  tff(c_478, plain, (![C_160, A_161, B_162]: (v4_relat_1(C_160, A_161) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.84/1.41  tff(c_486, plain, (v4_relat_1('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_461, c_478])).
% 2.84/1.41  tff(c_552, plain, (![B_183, A_184]: (k1_relat_1(B_183)=A_184 | ~v1_partfun1(B_183, A_184) | ~v4_relat_1(B_183, A_184) | ~v1_relat_1(B_183))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.84/1.41  tff(c_555, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_partfun1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_486, c_552])).
% 2.84/1.41  tff(c_558, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_partfun1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_468, c_555])).
% 2.84/1.41  tff(c_559, plain, (~v1_partfun1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_558])).
% 2.84/1.41  tff(c_527, plain, (![B_180, A_181]: (r1_tarski(k1_relat_1(B_180), A_181) | ~v4_relat_1(B_180, A_181) | ~v1_relat_1(B_180))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.84/1.41  tff(c_28, plain, (![A_21]: (r2_hidden('#skF_1'(A_21), A_21) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.84/1.41  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.41  tff(c_494, plain, (![C_166, B_167, A_168]: (~v1_xboole_0(C_166) | ~m1_subset_1(B_167, k1_zfmisc_1(C_166)) | ~r2_hidden(A_168, B_167))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.84/1.41  tff(c_502, plain, (![B_169, A_170, A_171]: (~v1_xboole_0(B_169) | ~r2_hidden(A_170, A_171) | ~r1_tarski(A_171, B_169))), inference(resolution, [status(thm)], [c_6, c_494])).
% 2.84/1.41  tff(c_505, plain, (![B_169, A_21]: (~v1_xboole_0(B_169) | ~r1_tarski(A_21, B_169) | k1_xboole_0=A_21)), inference(resolution, [status(thm)], [c_28, c_502])).
% 2.84/1.41  tff(c_575, plain, (![A_191, B_192]: (~v1_xboole_0(A_191) | k1_relat_1(B_192)=k1_xboole_0 | ~v4_relat_1(B_192, A_191) | ~v1_relat_1(B_192))), inference(resolution, [status(thm)], [c_527, c_505])).
% 2.84/1.41  tff(c_578, plain, (~v1_xboole_0(k1_xboole_0) | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_486, c_575])).
% 2.84/1.41  tff(c_581, plain, (~v1_xboole_0(k1_xboole_0) | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_468, c_578])).
% 2.84/1.41  tff(c_582, plain, (~v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_581])).
% 2.84/1.41  tff(c_439, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_435, c_46])).
% 2.84/1.41  tff(c_448, plain, (v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_437, c_439])).
% 2.84/1.41  tff(c_641, plain, (![C_217, A_218, B_219]: (v1_partfun1(C_217, A_218) | ~v1_funct_2(C_217, A_218, B_219) | ~v1_funct_1(C_217) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))) | v1_xboole_0(B_219))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.84/1.41  tff(c_644, plain, (v1_partfun1('#skF_4', k1_xboole_0) | ~v1_funct_2('#skF_4', k1_xboole_0, k1_xboole_0) | ~v1_funct_1('#skF_4') | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_461, c_641])).
% 2.84/1.41  tff(c_651, plain, (v1_partfun1('#skF_4', k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_448, c_644])).
% 2.84/1.41  tff(c_653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_582, c_559, c_651])).
% 2.84/1.41  tff(c_654, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_581])).
% 2.84/1.41  tff(c_34, plain, (![B_48]: (v1_partfun1(B_48, k1_relat_1(B_48)) | ~v4_relat_1(B_48, k1_relat_1(B_48)) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.84/1.41  tff(c_665, plain, (v1_partfun1('#skF_4', k1_relat_1('#skF_4')) | ~v4_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_654, c_34])).
% 2.84/1.41  tff(c_675, plain, (v1_partfun1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_468, c_486, c_654, c_665])).
% 2.84/1.41  tff(c_677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_559, c_675])).
% 2.84/1.41  tff(c_678, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_558])).
% 2.84/1.41  tff(c_735, plain, (![A_223, B_224, C_225]: (k1_relset_1(A_223, B_224, C_225)=k1_relat_1(C_225) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.84/1.41  tff(c_738, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_461, c_735])).
% 2.84/1.41  tff(c_744, plain, (k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_678, c_738])).
% 2.84/1.41  tff(c_771, plain, (![A_231, B_232, C_233]: (k8_relset_1(A_231, B_232, C_233, B_232)=k1_relset_1(A_231, B_232, C_233) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.84/1.41  tff(c_773, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4', k1_xboole_0)=k1_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_461, c_771])).
% 2.84/1.41  tff(c_778, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_4', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_744, c_773])).
% 2.84/1.41  tff(c_780, plain, $false, inference(negUnitSimplification, [status(thm)], [c_470, c_778])).
% 2.84/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.41  
% 2.84/1.41  Inference rules
% 2.84/1.41  ----------------------
% 2.84/1.41  #Ref     : 0
% 2.84/1.41  #Sup     : 153
% 2.84/1.41  #Fact    : 0
% 2.84/1.41  #Define  : 0
% 2.84/1.41  #Split   : 8
% 2.84/1.41  #Chain   : 0
% 2.84/1.41  #Close   : 0
% 2.84/1.41  
% 2.84/1.41  Ordering : KBO
% 2.84/1.41  
% 2.84/1.41  Simplification rules
% 2.84/1.41  ----------------------
% 2.84/1.41  #Subsume      : 7
% 2.84/1.41  #Demod        : 90
% 2.84/1.41  #Tautology    : 66
% 2.84/1.41  #SimpNegUnit  : 6
% 2.84/1.41  #BackRed      : 15
% 2.84/1.41  
% 2.84/1.41  #Partial instantiations: 0
% 2.84/1.41  #Strategies tried      : 1
% 2.84/1.41  
% 2.84/1.41  Timing (in seconds)
% 2.84/1.41  ----------------------
% 2.84/1.42  Preprocessing        : 0.33
% 2.84/1.42  Parsing              : 0.17
% 2.84/1.42  CNF conversion       : 0.02
% 2.84/1.42  Main loop            : 0.32
% 2.84/1.42  Inferencing          : 0.12
% 2.84/1.42  Reduction            : 0.10
% 2.84/1.42  Demodulation         : 0.07
% 2.84/1.42  BG Simplification    : 0.02
% 2.84/1.42  Subsumption          : 0.04
% 2.84/1.42  Abstraction          : 0.02
% 2.84/1.42  MUC search           : 0.00
% 2.84/1.42  Cooper               : 0.00
% 2.84/1.42  Total                : 0.69
% 2.84/1.42  Index Insertion      : 0.00
% 2.84/1.42  Index Deletion       : 0.00
% 2.84/1.42  Index Matching       : 0.00
% 2.84/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
