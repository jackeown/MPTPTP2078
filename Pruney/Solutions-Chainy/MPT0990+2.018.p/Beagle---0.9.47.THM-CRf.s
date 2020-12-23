%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:58 EST 2020

% Result     : Theorem 9.82s
% Output     : CNFRefutation 9.82s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 401 expanded)
%              Number of leaves         :   49 ( 160 expanded)
%              Depth                    :   17
%              Number of atoms          :  288 (1227 expanded)
%              Number of equality atoms :   76 ( 381 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_178,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_152,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_140,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_128,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_126,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_150,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_60,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_129,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_142,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_129])).

tff(c_194,plain,(
    ! [C_78,A_79,B_80] :
      ( v4_relat_1(C_78,A_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_206,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_194])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_141,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_129])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_24,plain,(
    ! [A_21] :
      ( v1_relat_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_66,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_70,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_340,plain,(
    ! [A_98,B_99,C_100] :
      ( k2_relset_1(A_98,B_99,C_100) = k2_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_346,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_340])).

tff(c_353,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_346])).

tff(c_227,plain,(
    ! [A_86] :
      ( k1_relat_1(k2_funct_1(A_86)) = k2_relat_1(A_86)
      | ~ v2_funct_1(A_86)
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k10_relat_1(B_4,A_3),k1_relat_1(B_4))
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4295,plain,(
    ! [A_276,A_277] :
      ( r1_tarski(k10_relat_1(k2_funct_1(A_276),A_277),k2_relat_1(A_276))
      | ~ v1_relat_1(k2_funct_1(A_276))
      | ~ v2_funct_1(A_276)
      | ~ v1_funct_1(A_276)
      | ~ v1_relat_1(A_276) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_6])).

tff(c_4313,plain,(
    ! [A_277] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_3'),A_277),'#skF_2')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_4295])).

tff(c_4325,plain,(
    ! [A_277] :
      ( r1_tarski(k10_relat_1(k2_funct_1('#skF_3'),A_277),'#skF_2')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_82,c_66,c_4313])).

tff(c_4816,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4325])).

tff(c_4819,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_4816])).

tff(c_4823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_82,c_4819])).

tff(c_4825,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4325])).

tff(c_205,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_194])).

tff(c_58,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_12,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    ! [A_15] : k1_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_12])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_2445,plain,(
    ! [C_199,A_197,F_201,D_200,E_202,B_198] :
      ( m1_subset_1(k1_partfun1(A_197,B_198,C_199,D_200,E_202,F_201),k1_zfmisc_1(k2_zfmisc_1(A_197,D_200)))
      | ~ m1_subset_1(F_201,k1_zfmisc_1(k2_zfmisc_1(C_199,D_200)))
      | ~ v1_funct_1(F_201)
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ v1_funct_1(E_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_50,plain,(
    ! [A_38] : m1_subset_1(k6_relat_1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_83,plain,(
    ! [A_38] : m1_subset_1(k6_partfun1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1388,plain,(
    ! [D_142,C_143,A_144,B_145] :
      ( D_142 = C_143
      | ~ r2_relset_1(A_144,B_145,C_143,D_142)
      | ~ m1_subset_1(D_142,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1396,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_1388])).

tff(c_1411,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1396])).

tff(c_1508,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1411])).

tff(c_2458,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2445,c_1508])).

tff(c_2480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_2458])).

tff(c_2481,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1411])).

tff(c_3302,plain,(
    ! [D_238,B_236,A_237,C_239,E_240,F_241] :
      ( k1_partfun1(A_237,B_236,C_239,D_238,E_240,F_241) = k5_relat_1(E_240,F_241)
      | ~ m1_subset_1(F_241,k1_zfmisc_1(k2_zfmisc_1(C_239,D_238)))
      | ~ v1_funct_1(F_241)
      | ~ m1_subset_1(E_240,k1_zfmisc_1(k2_zfmisc_1(A_237,B_236)))
      | ~ v1_funct_1(E_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_3308,plain,(
    ! [A_237,B_236,E_240] :
      ( k1_partfun1(A_237,B_236,'#skF_2','#skF_1',E_240,'#skF_4') = k5_relat_1(E_240,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_240,k1_zfmisc_1(k2_zfmisc_1(A_237,B_236)))
      | ~ v1_funct_1(E_240) ) ),
    inference(resolution,[status(thm)],[c_72,c_3302])).

tff(c_4169,plain,(
    ! [A_273,B_274,E_275] :
      ( k1_partfun1(A_273,B_274,'#skF_2','#skF_1',E_275,'#skF_4') = k5_relat_1(E_275,'#skF_4')
      | ~ m1_subset_1(E_275,k1_zfmisc_1(k2_zfmisc_1(A_273,B_274)))
      | ~ v1_funct_1(E_275) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3308])).

tff(c_4181,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_4169])).

tff(c_4192,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2481,c_4181])).

tff(c_589,plain,(
    ! [A_110,B_111] :
      ( k10_relat_1(A_110,k1_relat_1(B_111)) = k1_relat_1(k5_relat_1(A_110,B_111))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_599,plain,(
    ! [A_110,B_111] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_110,B_111)),k1_relat_1(A_110))
      | ~ v1_relat_1(A_110)
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_6])).

tff(c_4199,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1('#skF_1')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4192,c_599])).

tff(c_4206,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_142,c_141,c_92,c_4199])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_87,plain,(
    ! [A_22] : v1_relat_1(k6_partfun1(A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_26])).

tff(c_14,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_91,plain,(
    ! [A_15] : k2_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_14])).

tff(c_18,plain,(
    ! [B_19,A_18] :
      ( k5_relat_1(B_19,k6_relat_1(A_18)) = B_19
      | ~ r1_tarski(k2_relat_1(B_19),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_277,plain,(
    ! [B_92,A_93] :
      ( k5_relat_1(B_92,k6_partfun1(A_93)) = B_92
      | ~ r1_tarski(k2_relat_1(B_92),A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_18])).

tff(c_284,plain,(
    ! [A_15,A_93] :
      ( k5_relat_1(k6_partfun1(A_15),k6_partfun1(A_93)) = k6_partfun1(A_15)
      | ~ r1_tarski(A_15,A_93)
      | ~ v1_relat_1(k6_partfun1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_277])).

tff(c_287,plain,(
    ! [A_15,A_93] :
      ( k5_relat_1(k6_partfun1(A_15),k6_partfun1(A_93)) = k6_partfun1(A_15)
      | ~ r1_tarski(A_15,A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_284])).

tff(c_608,plain,(
    ! [A_110,A_15] :
      ( k1_relat_1(k5_relat_1(A_110,k6_partfun1(A_15))) = k10_relat_1(A_110,A_15)
      | ~ v1_relat_1(k6_partfun1(A_15))
      | ~ v1_relat_1(A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_589])).

tff(c_652,plain,(
    ! [A_114,A_115] :
      ( k1_relat_1(k5_relat_1(A_114,k6_partfun1(A_115))) = k10_relat_1(A_114,A_115)
      | ~ v1_relat_1(A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_608])).

tff(c_703,plain,(
    ! [A_15,A_93] :
      ( k10_relat_1(k6_partfun1(A_15),A_93) = k1_relat_1(k6_partfun1(A_15))
      | ~ v1_relat_1(k6_partfun1(A_15))
      | ~ r1_tarski(A_15,A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_652])).

tff(c_825,plain,(
    ! [A_120,A_121] :
      ( k10_relat_1(k6_partfun1(A_120),A_121) = A_120
      | ~ r1_tarski(A_120,A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_92,c_703])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( k5_relat_1(k6_relat_1(A_16),B_17) = B_17
      | ~ r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_421,plain,(
    ! [A_103,B_104] :
      ( k5_relat_1(k6_partfun1(A_103),B_104) = B_104
      | ~ r1_tarski(k1_relat_1(B_104),A_103)
      | ~ v1_relat_1(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_16])).

tff(c_434,plain,(
    ! [A_103,A_15] :
      ( k5_relat_1(k6_partfun1(A_103),k6_partfun1(A_15)) = k6_partfun1(A_15)
      | ~ r1_tarski(A_15,A_103)
      | ~ v1_relat_1(k6_partfun1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_421])).

tff(c_438,plain,(
    ! [A_103,A_15] :
      ( k5_relat_1(k6_partfun1(A_103),k6_partfun1(A_15)) = k6_partfun1(A_15)
      | ~ r1_tarski(A_15,A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_434])).

tff(c_686,plain,(
    ! [A_103,A_15] :
      ( k10_relat_1(k6_partfun1(A_103),A_15) = k1_relat_1(k6_partfun1(A_15))
      | ~ v1_relat_1(k6_partfun1(A_103))
      | ~ r1_tarski(A_15,A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_652])).

tff(c_715,plain,(
    ! [A_103,A_15] :
      ( k10_relat_1(k6_partfun1(A_103),A_15) = A_15
      | ~ r1_tarski(A_15,A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_92,c_686])).

tff(c_957,plain,(
    ! [A_127,A_126] :
      ( A_127 = A_126
      | ~ r1_tarski(A_126,A_127)
      | ~ r1_tarski(A_127,A_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_715])).

tff(c_973,plain,(
    ! [B_2,A_1] :
      ( k1_relat_1(B_2) = A_1
      | ~ r1_tarski(A_1,k1_relat_1(B_2))
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_957])).

tff(c_4212,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4206,c_973])).

tff(c_4219,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_205,c_4212])).

tff(c_325,plain,(
    ! [A_97] :
      ( k2_relat_1(k2_funct_1(A_97)) = k1_relat_1(A_97)
      | ~ v2_funct_1(A_97)
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_20,plain,(
    ! [A_20] :
      ( k5_relat_1(A_20,k6_relat_1(k2_relat_1(A_20))) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_88,plain,(
    ! [A_20] :
      ( k5_relat_1(A_20,k6_partfun1(k2_relat_1(A_20))) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_20])).

tff(c_4576,plain,(
    ! [A_285] :
      ( k5_relat_1(k2_funct_1(A_285),k6_partfun1(k1_relat_1(A_285))) = k2_funct_1(A_285)
      | ~ v1_relat_1(k2_funct_1(A_285))
      | ~ v2_funct_1(A_285)
      | ~ v1_funct_1(A_285)
      | ~ v1_relat_1(A_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_88])).

tff(c_4594,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4219,c_4576])).

tff(c_4620,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_82,c_66,c_4594])).

tff(c_6501,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4825,c_4620])).

tff(c_34,plain,(
    ! [A_24] :
      ( k5_relat_1(k2_funct_1(A_24),A_24) = k6_relat_1(k2_relat_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_85,plain,(
    ! [A_24] :
      ( k5_relat_1(k2_funct_1(A_24),A_24) = k6_partfun1(k2_relat_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_34])).

tff(c_881,plain,(
    ! [A_123,B_124,C_125] :
      ( k5_relat_1(k5_relat_1(A_123,B_124),C_125) = k5_relat_1(A_123,k5_relat_1(B_124,C_125))
      | ~ v1_relat_1(C_125)
      | ~ v1_relat_1(B_124)
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8384,plain,(
    ! [A_357,C_358] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_357)),C_358) = k5_relat_1(k2_funct_1(A_357),k5_relat_1(A_357,C_358))
      | ~ v1_relat_1(C_358)
      | ~ v1_relat_1(A_357)
      | ~ v1_relat_1(k2_funct_1(A_357))
      | ~ v2_funct_1(A_357)
      | ~ v1_funct_1(A_357)
      | ~ v1_relat_1(A_357) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_881])).

tff(c_8629,plain,(
    ! [C_358] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_358)) = k5_relat_1(k6_partfun1('#skF_2'),C_358)
      | ~ v1_relat_1(C_358)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_8384])).

tff(c_11875,plain,(
    ! [C_448] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_448)) = k5_relat_1(k6_partfun1('#skF_2'),C_448)
      | ~ v1_relat_1(C_448) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_82,c_66,c_4825,c_141,c_8629])).

tff(c_11956,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4192,c_11875])).

tff(c_12019,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_6501,c_11956])).

tff(c_436,plain,(
    ! [A_1,B_2] :
      ( k5_relat_1(k6_partfun1(A_1),B_2) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_421])).

tff(c_12176,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12019,c_436])).

tff(c_12207,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_206,c_12176])).

tff(c_12209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_12207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.82/3.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.82/3.59  
% 9.82/3.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.82/3.59  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.82/3.59  
% 9.82/3.59  %Foreground sorts:
% 9.82/3.59  
% 9.82/3.59  
% 9.82/3.59  %Background operators:
% 9.82/3.59  
% 9.82/3.59  
% 9.82/3.59  %Foreground operators:
% 9.82/3.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.82/3.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.82/3.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.82/3.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.82/3.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.82/3.59  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.82/3.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.82/3.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.82/3.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.82/3.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.82/3.59  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.82/3.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.82/3.59  tff('#skF_2', type, '#skF_2': $i).
% 9.82/3.59  tff('#skF_3', type, '#skF_3': $i).
% 9.82/3.59  tff('#skF_1', type, '#skF_1': $i).
% 9.82/3.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.82/3.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.82/3.59  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.82/3.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.82/3.59  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.82/3.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.82/3.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.82/3.59  tff('#skF_4', type, '#skF_4': $i).
% 9.82/3.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.82/3.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.82/3.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.82/3.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.82/3.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.82/3.59  
% 9.82/3.61  tff(f_178, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 9.82/3.61  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.82/3.61  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.82/3.61  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.82/3.61  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.82/3.61  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.82/3.61  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 9.82/3.61  tff(f_152, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.82/3.61  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.82/3.61  tff(f_140, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.82/3.61  tff(f_128, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 9.82/3.61  tff(f_126, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.82/3.61  tff(f_150, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.82/3.61  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 9.82/3.61  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.82/3.61  tff(f_84, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 9.82/3.61  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 9.82/3.61  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 9.82/3.61  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 9.82/3.61  tff(f_104, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 9.82/3.61  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 9.82/3.61  tff(c_60, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_178])).
% 9.82/3.61  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 9.82/3.61  tff(c_129, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.82/3.61  tff(c_142, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_129])).
% 9.82/3.61  tff(c_194, plain, (![C_78, A_79, B_80]: (v4_relat_1(C_78, A_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.82/3.61  tff(c_206, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_194])).
% 9.82/3.61  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 9.82/3.61  tff(c_141, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_129])).
% 9.82/3.61  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 9.82/3.61  tff(c_24, plain, (![A_21]: (v1_relat_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.82/3.61  tff(c_66, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 9.82/3.61  tff(c_70, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_178])).
% 9.82/3.61  tff(c_340, plain, (![A_98, B_99, C_100]: (k2_relset_1(A_98, B_99, C_100)=k2_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.82/3.61  tff(c_346, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_340])).
% 9.82/3.61  tff(c_353, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_346])).
% 9.82/3.61  tff(c_227, plain, (![A_86]: (k1_relat_1(k2_funct_1(A_86))=k2_relat_1(A_86) | ~v2_funct_1(A_86) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.82/3.61  tff(c_6, plain, (![B_4, A_3]: (r1_tarski(k10_relat_1(B_4, A_3), k1_relat_1(B_4)) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.82/3.61  tff(c_4295, plain, (![A_276, A_277]: (r1_tarski(k10_relat_1(k2_funct_1(A_276), A_277), k2_relat_1(A_276)) | ~v1_relat_1(k2_funct_1(A_276)) | ~v2_funct_1(A_276) | ~v1_funct_1(A_276) | ~v1_relat_1(A_276))), inference(superposition, [status(thm), theory('equality')], [c_227, c_6])).
% 9.82/3.61  tff(c_4313, plain, (![A_277]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_3'), A_277), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_353, c_4295])).
% 9.82/3.61  tff(c_4325, plain, (![A_277]: (r1_tarski(k10_relat_1(k2_funct_1('#skF_3'), A_277), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_82, c_66, c_4313])).
% 9.82/3.61  tff(c_4816, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4325])).
% 9.82/3.61  tff(c_4819, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_4816])).
% 9.82/3.61  tff(c_4823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_82, c_4819])).
% 9.82/3.61  tff(c_4825, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_4325])).
% 9.82/3.61  tff(c_205, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_194])).
% 9.82/3.61  tff(c_58, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.82/3.61  tff(c_12, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.82/3.61  tff(c_92, plain, (![A_15]: (k1_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_12])).
% 9.82/3.61  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_178])).
% 9.82/3.61  tff(c_2445, plain, (![C_199, A_197, F_201, D_200, E_202, B_198]: (m1_subset_1(k1_partfun1(A_197, B_198, C_199, D_200, E_202, F_201), k1_zfmisc_1(k2_zfmisc_1(A_197, D_200))) | ~m1_subset_1(F_201, k1_zfmisc_1(k2_zfmisc_1(C_199, D_200))) | ~v1_funct_1(F_201) | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~v1_funct_1(E_202))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.82/3.61  tff(c_50, plain, (![A_38]: (m1_subset_1(k6_relat_1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.82/3.61  tff(c_83, plain, (![A_38]: (m1_subset_1(k6_partfun1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_50])).
% 9.82/3.61  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 9.82/3.61  tff(c_1388, plain, (![D_142, C_143, A_144, B_145]: (D_142=C_143 | ~r2_relset_1(A_144, B_145, C_143, D_142) | ~m1_subset_1(D_142, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.82/3.61  tff(c_1396, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_1388])).
% 9.82/3.61  tff(c_1411, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1396])).
% 9.82/3.61  tff(c_1508, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1411])).
% 9.82/3.61  tff(c_2458, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2445, c_1508])).
% 9.82/3.61  tff(c_2480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_2458])).
% 9.82/3.61  tff(c_2481, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1411])).
% 9.82/3.61  tff(c_3302, plain, (![D_238, B_236, A_237, C_239, E_240, F_241]: (k1_partfun1(A_237, B_236, C_239, D_238, E_240, F_241)=k5_relat_1(E_240, F_241) | ~m1_subset_1(F_241, k1_zfmisc_1(k2_zfmisc_1(C_239, D_238))) | ~v1_funct_1(F_241) | ~m1_subset_1(E_240, k1_zfmisc_1(k2_zfmisc_1(A_237, B_236))) | ~v1_funct_1(E_240))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.82/3.61  tff(c_3308, plain, (![A_237, B_236, E_240]: (k1_partfun1(A_237, B_236, '#skF_2', '#skF_1', E_240, '#skF_4')=k5_relat_1(E_240, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_240, k1_zfmisc_1(k2_zfmisc_1(A_237, B_236))) | ~v1_funct_1(E_240))), inference(resolution, [status(thm)], [c_72, c_3302])).
% 9.82/3.61  tff(c_4169, plain, (![A_273, B_274, E_275]: (k1_partfun1(A_273, B_274, '#skF_2', '#skF_1', E_275, '#skF_4')=k5_relat_1(E_275, '#skF_4') | ~m1_subset_1(E_275, k1_zfmisc_1(k2_zfmisc_1(A_273, B_274))) | ~v1_funct_1(E_275))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3308])).
% 9.82/3.61  tff(c_4181, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_4169])).
% 9.82/3.61  tff(c_4192, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2481, c_4181])).
% 9.82/3.61  tff(c_589, plain, (![A_110, B_111]: (k10_relat_1(A_110, k1_relat_1(B_111))=k1_relat_1(k5_relat_1(A_110, B_111)) | ~v1_relat_1(B_111) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.82/3.61  tff(c_599, plain, (![A_110, B_111]: (r1_tarski(k1_relat_1(k5_relat_1(A_110, B_111)), k1_relat_1(A_110)) | ~v1_relat_1(A_110) | ~v1_relat_1(B_111) | ~v1_relat_1(A_110))), inference(superposition, [status(thm), theory('equality')], [c_589, c_6])).
% 9.82/3.61  tff(c_4199, plain, (r1_tarski(k1_relat_1(k6_partfun1('#skF_1')), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4192, c_599])).
% 9.82/3.61  tff(c_4206, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_142, c_141, c_92, c_4199])).
% 9.82/3.61  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.82/3.61  tff(c_26, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.82/3.61  tff(c_87, plain, (![A_22]: (v1_relat_1(k6_partfun1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_26])).
% 9.82/3.61  tff(c_14, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.82/3.61  tff(c_91, plain, (![A_15]: (k2_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_14])).
% 9.82/3.61  tff(c_18, plain, (![B_19, A_18]: (k5_relat_1(B_19, k6_relat_1(A_18))=B_19 | ~r1_tarski(k2_relat_1(B_19), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.82/3.61  tff(c_277, plain, (![B_92, A_93]: (k5_relat_1(B_92, k6_partfun1(A_93))=B_92 | ~r1_tarski(k2_relat_1(B_92), A_93) | ~v1_relat_1(B_92))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_18])).
% 9.82/3.61  tff(c_284, plain, (![A_15, A_93]: (k5_relat_1(k6_partfun1(A_15), k6_partfun1(A_93))=k6_partfun1(A_15) | ~r1_tarski(A_15, A_93) | ~v1_relat_1(k6_partfun1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_91, c_277])).
% 9.82/3.61  tff(c_287, plain, (![A_15, A_93]: (k5_relat_1(k6_partfun1(A_15), k6_partfun1(A_93))=k6_partfun1(A_15) | ~r1_tarski(A_15, A_93))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_284])).
% 9.82/3.61  tff(c_608, plain, (![A_110, A_15]: (k1_relat_1(k5_relat_1(A_110, k6_partfun1(A_15)))=k10_relat_1(A_110, A_15) | ~v1_relat_1(k6_partfun1(A_15)) | ~v1_relat_1(A_110))), inference(superposition, [status(thm), theory('equality')], [c_92, c_589])).
% 9.82/3.61  tff(c_652, plain, (![A_114, A_115]: (k1_relat_1(k5_relat_1(A_114, k6_partfun1(A_115)))=k10_relat_1(A_114, A_115) | ~v1_relat_1(A_114))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_608])).
% 9.82/3.61  tff(c_703, plain, (![A_15, A_93]: (k10_relat_1(k6_partfun1(A_15), A_93)=k1_relat_1(k6_partfun1(A_15)) | ~v1_relat_1(k6_partfun1(A_15)) | ~r1_tarski(A_15, A_93))), inference(superposition, [status(thm), theory('equality')], [c_287, c_652])).
% 9.82/3.61  tff(c_825, plain, (![A_120, A_121]: (k10_relat_1(k6_partfun1(A_120), A_121)=A_120 | ~r1_tarski(A_120, A_121))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_92, c_703])).
% 9.82/3.61  tff(c_16, plain, (![A_16, B_17]: (k5_relat_1(k6_relat_1(A_16), B_17)=B_17 | ~r1_tarski(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.82/3.61  tff(c_421, plain, (![A_103, B_104]: (k5_relat_1(k6_partfun1(A_103), B_104)=B_104 | ~r1_tarski(k1_relat_1(B_104), A_103) | ~v1_relat_1(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_16])).
% 9.82/3.61  tff(c_434, plain, (![A_103, A_15]: (k5_relat_1(k6_partfun1(A_103), k6_partfun1(A_15))=k6_partfun1(A_15) | ~r1_tarski(A_15, A_103) | ~v1_relat_1(k6_partfun1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_421])).
% 9.82/3.61  tff(c_438, plain, (![A_103, A_15]: (k5_relat_1(k6_partfun1(A_103), k6_partfun1(A_15))=k6_partfun1(A_15) | ~r1_tarski(A_15, A_103))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_434])).
% 9.82/3.61  tff(c_686, plain, (![A_103, A_15]: (k10_relat_1(k6_partfun1(A_103), A_15)=k1_relat_1(k6_partfun1(A_15)) | ~v1_relat_1(k6_partfun1(A_103)) | ~r1_tarski(A_15, A_103))), inference(superposition, [status(thm), theory('equality')], [c_438, c_652])).
% 9.82/3.61  tff(c_715, plain, (![A_103, A_15]: (k10_relat_1(k6_partfun1(A_103), A_15)=A_15 | ~r1_tarski(A_15, A_103))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_92, c_686])).
% 9.82/3.61  tff(c_957, plain, (![A_127, A_126]: (A_127=A_126 | ~r1_tarski(A_126, A_127) | ~r1_tarski(A_127, A_126))), inference(superposition, [status(thm), theory('equality')], [c_825, c_715])).
% 9.82/3.61  tff(c_973, plain, (![B_2, A_1]: (k1_relat_1(B_2)=A_1 | ~r1_tarski(A_1, k1_relat_1(B_2)) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_957])).
% 9.82/3.61  tff(c_4212, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4206, c_973])).
% 9.82/3.61  tff(c_4219, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_205, c_4212])).
% 9.82/3.61  tff(c_325, plain, (![A_97]: (k2_relat_1(k2_funct_1(A_97))=k1_relat_1(A_97) | ~v2_funct_1(A_97) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.82/3.61  tff(c_20, plain, (![A_20]: (k5_relat_1(A_20, k6_relat_1(k2_relat_1(A_20)))=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.82/3.61  tff(c_88, plain, (![A_20]: (k5_relat_1(A_20, k6_partfun1(k2_relat_1(A_20)))=A_20 | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_20])).
% 9.82/3.61  tff(c_4576, plain, (![A_285]: (k5_relat_1(k2_funct_1(A_285), k6_partfun1(k1_relat_1(A_285)))=k2_funct_1(A_285) | ~v1_relat_1(k2_funct_1(A_285)) | ~v2_funct_1(A_285) | ~v1_funct_1(A_285) | ~v1_relat_1(A_285))), inference(superposition, [status(thm), theory('equality')], [c_325, c_88])).
% 9.82/3.61  tff(c_4594, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4219, c_4576])).
% 9.82/3.61  tff(c_4620, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_82, c_66, c_4594])).
% 9.82/3.61  tff(c_6501, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4825, c_4620])).
% 9.82/3.61  tff(c_34, plain, (![A_24]: (k5_relat_1(k2_funct_1(A_24), A_24)=k6_relat_1(k2_relat_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.82/3.61  tff(c_85, plain, (![A_24]: (k5_relat_1(k2_funct_1(A_24), A_24)=k6_partfun1(k2_relat_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_34])).
% 9.82/3.61  tff(c_881, plain, (![A_123, B_124, C_125]: (k5_relat_1(k5_relat_1(A_123, B_124), C_125)=k5_relat_1(A_123, k5_relat_1(B_124, C_125)) | ~v1_relat_1(C_125) | ~v1_relat_1(B_124) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.82/3.61  tff(c_8384, plain, (![A_357, C_358]: (k5_relat_1(k6_partfun1(k2_relat_1(A_357)), C_358)=k5_relat_1(k2_funct_1(A_357), k5_relat_1(A_357, C_358)) | ~v1_relat_1(C_358) | ~v1_relat_1(A_357) | ~v1_relat_1(k2_funct_1(A_357)) | ~v2_funct_1(A_357) | ~v1_funct_1(A_357) | ~v1_relat_1(A_357))), inference(superposition, [status(thm), theory('equality')], [c_85, c_881])).
% 9.82/3.61  tff(c_8629, plain, (![C_358]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_358))=k5_relat_1(k6_partfun1('#skF_2'), C_358) | ~v1_relat_1(C_358) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_353, c_8384])).
% 9.82/3.61  tff(c_11875, plain, (![C_448]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_448))=k5_relat_1(k6_partfun1('#skF_2'), C_448) | ~v1_relat_1(C_448))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_82, c_66, c_4825, c_141, c_8629])).
% 9.82/3.61  tff(c_11956, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4192, c_11875])).
% 9.82/3.61  tff(c_12019, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_6501, c_11956])).
% 9.82/3.61  tff(c_436, plain, (![A_1, B_2]: (k5_relat_1(k6_partfun1(A_1), B_2)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_421])).
% 9.82/3.61  tff(c_12176, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12019, c_436])).
% 9.82/3.61  tff(c_12207, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_206, c_12176])).
% 9.82/3.61  tff(c_12209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_12207])).
% 9.82/3.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.82/3.61  
% 9.82/3.61  Inference rules
% 9.82/3.61  ----------------------
% 9.82/3.61  #Ref     : 0
% 9.82/3.61  #Sup     : 2575
% 9.82/3.61  #Fact    : 0
% 9.82/3.61  #Define  : 0
% 9.82/3.61  #Split   : 8
% 9.82/3.61  #Chain   : 0
% 9.82/3.61  #Close   : 0
% 9.82/3.61  
% 9.82/3.61  Ordering : KBO
% 9.82/3.61  
% 9.82/3.61  Simplification rules
% 9.82/3.61  ----------------------
% 9.82/3.61  #Subsume      : 242
% 9.82/3.61  #Demod        : 4141
% 9.82/3.61  #Tautology    : 948
% 9.82/3.61  #SimpNegUnit  : 1
% 9.82/3.61  #BackRed      : 20
% 9.82/3.61  
% 9.82/3.61  #Partial instantiations: 0
% 9.82/3.61  #Strategies tried      : 1
% 9.82/3.61  
% 9.82/3.61  Timing (in seconds)
% 9.82/3.61  ----------------------
% 9.82/3.62  Preprocessing        : 0.37
% 9.82/3.62  Parsing              : 0.20
% 9.82/3.62  CNF conversion       : 0.03
% 9.82/3.62  Main loop            : 2.46
% 9.82/3.62  Inferencing          : 0.69
% 9.82/3.62  Reduction            : 1.08
% 9.82/3.62  Demodulation         : 0.87
% 9.82/3.62  BG Simplification    : 0.08
% 9.82/3.62  Subsumption          : 0.48
% 9.82/3.62  Abstraction          : 0.11
% 9.82/3.62  MUC search           : 0.00
% 9.82/3.62  Cooper               : 0.00
% 9.82/3.62  Total                : 2.88
% 9.82/3.62  Index Insertion      : 0.00
% 9.82/3.62  Index Deletion       : 0.00
% 9.82/3.62  Index Matching       : 0.00
% 9.82/3.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
