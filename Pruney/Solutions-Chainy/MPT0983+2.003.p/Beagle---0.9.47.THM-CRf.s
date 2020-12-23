%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:01 EST 2020

% Result     : Theorem 9.42s
% Output     : CNFRefutation 9.42s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 365 expanded)
%              Number of leaves         :   51 ( 144 expanded)
%              Depth                    :   12
%              Number of atoms          :  300 (1134 expanded)
%              Number of equality atoms :   56 ( 135 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_190,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_128,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_232,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_188,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_166,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_170,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_146,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_126,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_212,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_178,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v1_xboole_0(k6_relat_1(A))
        & v1_relat_1(k6_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_116,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_138,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_154,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_88,plain,(
    ! [A_54] : k6_relat_1(A_54) = k6_partfun1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_58,plain,(
    ! [A_27] : v2_funct_1(k6_relat_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_111,plain,(
    ! [A_27] : v2_funct_1(k6_partfun1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_58])).

tff(c_108,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_104,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_102,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_98,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_2252,plain,(
    ! [E_206,B_203,F_201,C_205,A_204,D_202] :
      ( k1_partfun1(A_204,B_203,C_205,D_202,E_206,F_201) = k5_relat_1(E_206,F_201)
      | ~ m1_subset_1(F_201,k1_zfmisc_1(k2_zfmisc_1(C_205,D_202)))
      | ~ v1_funct_1(F_201)
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203)))
      | ~ v1_funct_1(E_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_2262,plain,(
    ! [A_204,B_203,E_206] :
      ( k1_partfun1(A_204,B_203,'#skF_2','#skF_1',E_206,'#skF_4') = k5_relat_1(E_206,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_203)))
      | ~ v1_funct_1(E_206) ) ),
    inference(resolution,[status(thm)],[c_98,c_2252])).

tff(c_4434,plain,(
    ! [A_285,B_286,E_287] :
      ( k1_partfun1(A_285,B_286,'#skF_2','#skF_1',E_287,'#skF_4') = k5_relat_1(E_287,'#skF_4')
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286)))
      | ~ v1_funct_1(E_287) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_2262])).

tff(c_4470,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_4434])).

tff(c_4478,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_4470])).

tff(c_74,plain,(
    ! [E_44,C_42,F_45,A_40,D_43,B_41] :
      ( m1_subset_1(k1_partfun1(A_40,B_41,C_42,D_43,E_44,F_45),k1_zfmisc_1(k2_zfmisc_1(A_40,D_43)))
      | ~ m1_subset_1(F_45,k1_zfmisc_1(k2_zfmisc_1(C_42,D_43)))
      | ~ v1_funct_1(F_45)
      | ~ m1_subset_1(E_44,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_1(E_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_5678,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4478,c_74])).

tff(c_5685,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_104,c_102,c_98,c_5678])).

tff(c_80,plain,(
    ! [A_46] : m1_subset_1(k6_partfun1(A_46),k1_zfmisc_1(k2_zfmisc_1(A_46,A_46))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_96,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_1503,plain,(
    ! [D_172,C_173,A_174,B_175] :
      ( D_172 = C_173
      | ~ r2_relset_1(A_174,B_175,C_173,D_172)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1509,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_96,c_1503])).

tff(c_1520,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1509])).

tff(c_7390,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5685,c_4478,c_4478,c_1520])).

tff(c_94,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_164,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_38,plain,(
    ! [A_22] : k2_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_118,plain,(
    ! [A_22] : k2_relat_1(k6_partfun1(A_22)) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_38])).

tff(c_54,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_113,plain,(
    ! [A_26] : v1_relat_1(k6_partfun1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_54])).

tff(c_416,plain,(
    ! [A_99] :
      ( k2_relat_1(A_99) != k1_xboole_0
      | k1_xboole_0 = A_99
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_428,plain,(
    ! [A_26] :
      ( k2_relat_1(k6_partfun1(A_26)) != k1_xboole_0
      | k6_partfun1(A_26) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_113,c_416])).

tff(c_465,plain,(
    ! [A_101] :
      ( k1_xboole_0 != A_101
      | k6_partfun1(A_101) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_428])).

tff(c_477,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_96])).

tff(c_571,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_477])).

tff(c_106,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_100,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_92,plain,(
    ! [B_56,C_57,A_55,E_60,D_58] :
      ( k1_xboole_0 = C_57
      | v2_funct_1(D_58)
      | ~ v2_funct_1(k1_partfun1(A_55,B_56,B_56,C_57,D_58,E_60))
      | ~ m1_subset_1(E_60,k1_zfmisc_1(k2_zfmisc_1(B_56,C_57)))
      | ~ v1_funct_2(E_60,B_56,C_57)
      | ~ v1_funct_1(E_60)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56)))
      | ~ v1_funct_2(D_58,A_55,B_56)
      | ~ v1_funct_1(D_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_5675,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4478,c_92])).

tff(c_5682,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_104,c_102,c_100,c_98,c_5675])).

tff(c_5683,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_571,c_5682])).

tff(c_7396,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7390,c_5683])).

tff(c_7406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_7396])).

tff(c_7408,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_477])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_84,plain,(
    ! [A_47] :
      ( ~ v1_xboole_0(k6_relat_1(A_47))
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_109,plain,(
    ! [A_47] :
      ( ~ v1_xboole_0(k6_partfun1(A_47))
      | v1_xboole_0(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84])).

tff(c_480,plain,(
    ! [A_101] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(A_101)
      | k1_xboole_0 != A_101 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_109])).

tff(c_506,plain,(
    ! [A_101] :
      ( v1_xboole_0(A_101)
      | k1_xboole_0 != A_101 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_480])).

tff(c_7456,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7408,c_506])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( v1_xboole_0(k2_zfmisc_1(A_7,B_8))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_7543,plain,(
    ! [A_356] :
      ( v2_funct_1(A_356)
      | ~ v1_funct_1(A_356)
      | ~ v1_relat_1(A_356)
      | ~ v1_xboole_0(A_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_7546,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_7543,c_164])).

tff(c_7549,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_7546])).

tff(c_7550,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_7549])).

tff(c_7432,plain,(
    ! [B_352,A_353] :
      ( v1_xboole_0(B_352)
      | ~ m1_subset_1(B_352,k1_zfmisc_1(A_353))
      | ~ v1_xboole_0(A_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7444,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_104,c_7432])).

tff(c_7555,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_7550,c_7444])).

tff(c_7564,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_7555])).

tff(c_7570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7456,c_7564])).

tff(c_7571,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_7549])).

tff(c_7572,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_7549])).

tff(c_18,plain,(
    ! [A_12] :
      ( v1_relat_1(A_12)
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7580,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7572,c_18])).

tff(c_7589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7571,c_7580])).

tff(c_7590,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_8431,plain,(
    ! [C_419,A_420,B_421] :
      ( v1_relat_1(C_419)
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(A_420,B_421))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_8448,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_8431])).

tff(c_8726,plain,(
    ! [C_436,B_437,A_438] :
      ( v5_relat_1(C_436,B_437)
      | ~ m1_subset_1(C_436,k1_zfmisc_1(k2_zfmisc_1(A_438,B_437))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_8745,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_98,c_8726])).

tff(c_8447,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_8431])).

tff(c_10026,plain,(
    ! [C_503,D_500,B_501,A_502,F_499,E_504] :
      ( k1_partfun1(A_502,B_501,C_503,D_500,E_504,F_499) = k5_relat_1(E_504,F_499)
      | ~ m1_subset_1(F_499,k1_zfmisc_1(k2_zfmisc_1(C_503,D_500)))
      | ~ v1_funct_1(F_499)
      | ~ m1_subset_1(E_504,k1_zfmisc_1(k2_zfmisc_1(A_502,B_501)))
      | ~ v1_funct_1(E_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_10042,plain,(
    ! [A_502,B_501,E_504] :
      ( k1_partfun1(A_502,B_501,'#skF_2','#skF_1',E_504,'#skF_4') = k5_relat_1(E_504,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_504,k1_zfmisc_1(k2_zfmisc_1(A_502,B_501)))
      | ~ v1_funct_1(E_504) ) ),
    inference(resolution,[status(thm)],[c_98,c_10026])).

tff(c_12301,plain,(
    ! [A_583,B_584,E_585] :
      ( k1_partfun1(A_583,B_584,'#skF_2','#skF_1',E_585,'#skF_4') = k5_relat_1(E_585,'#skF_4')
      | ~ m1_subset_1(E_585,k1_zfmisc_1(k2_zfmisc_1(A_583,B_584)))
      | ~ v1_funct_1(E_585) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_10042])).

tff(c_12334,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_12301])).

tff(c_12342,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_12334])).

tff(c_9238,plain,(
    ! [D_466,C_467,A_468,B_469] :
      ( D_466 = C_467
      | ~ r2_relset_1(A_468,B_469,C_467,D_466)
      | ~ m1_subset_1(D_466,k1_zfmisc_1(k2_zfmisc_1(A_468,B_469)))
      | ~ m1_subset_1(C_467,k1_zfmisc_1(k2_zfmisc_1(A_468,B_469))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_9246,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_96,c_9238])).

tff(c_9261,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_9246])).

tff(c_9382,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_9261])).

tff(c_13023,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12342,c_9382])).

tff(c_12833,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12342,c_74])).

tff(c_12840,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_104,c_102,c_98,c_12833])).

tff(c_13552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13023,c_12840])).

tff(c_13553,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_9261])).

tff(c_14096,plain,(
    ! [A_645,B_644,D_643,F_642,E_647,C_646] :
      ( k1_partfun1(A_645,B_644,C_646,D_643,E_647,F_642) = k5_relat_1(E_647,F_642)
      | ~ m1_subset_1(F_642,k1_zfmisc_1(k2_zfmisc_1(C_646,D_643)))
      | ~ v1_funct_1(F_642)
      | ~ m1_subset_1(E_647,k1_zfmisc_1(k2_zfmisc_1(A_645,B_644)))
      | ~ v1_funct_1(E_647) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_14110,plain,(
    ! [A_645,B_644,E_647] :
      ( k1_partfun1(A_645,B_644,'#skF_2','#skF_1',E_647,'#skF_4') = k5_relat_1(E_647,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_647,k1_zfmisc_1(k2_zfmisc_1(A_645,B_644)))
      | ~ v1_funct_1(E_647) ) ),
    inference(resolution,[status(thm)],[c_98,c_14096])).

tff(c_17007,plain,(
    ! [A_741,B_742,E_743] :
      ( k1_partfun1(A_741,B_742,'#skF_2','#skF_1',E_743,'#skF_4') = k5_relat_1(E_743,'#skF_4')
      | ~ m1_subset_1(E_743,k1_zfmisc_1(k2_zfmisc_1(A_741,B_742)))
      | ~ v1_funct_1(E_743) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_14110])).

tff(c_17043,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_17007])).

tff(c_17054,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_13553,c_17043])).

tff(c_30,plain,(
    ! [A_18,B_20] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_18,B_20)),k2_relat_1(B_20))
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_17070,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_17054,c_30])).

tff(c_17090,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8447,c_8448,c_118,c_17070])).

tff(c_8486,plain,(
    ! [B_425,A_426] :
      ( r1_tarski(k2_relat_1(B_425),A_426)
      | ~ v5_relat_1(B_425,A_426)
      | ~ v1_relat_1(B_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8496,plain,(
    ! [B_425,A_426] :
      ( k2_relat_1(B_425) = A_426
      | ~ r1_tarski(A_426,k2_relat_1(B_425))
      | ~ v5_relat_1(B_425,A_426)
      | ~ v1_relat_1(B_425) ) ),
    inference(resolution,[status(thm)],[c_8486,c_4])).

tff(c_17104,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_17090,c_8496])).

tff(c_17109,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8448,c_8745,c_17104])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8468,plain,(
    ! [B_422,A_423] :
      ( v5_relat_1(B_422,A_423)
      | ~ r1_tarski(k2_relat_1(B_422),A_423)
      | ~ v1_relat_1(B_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8478,plain,(
    ! [B_422] :
      ( v5_relat_1(B_422,k2_relat_1(B_422))
      | ~ v1_relat_1(B_422) ) ),
    inference(resolution,[status(thm)],[c_8,c_8468])).

tff(c_8788,plain,(
    ! [B_442] :
      ( v2_funct_2(B_442,k2_relat_1(B_442))
      | ~ v5_relat_1(B_442,k2_relat_1(B_442))
      | ~ v1_relat_1(B_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_8799,plain,(
    ! [B_422] :
      ( v2_funct_2(B_422,k2_relat_1(B_422))
      | ~ v1_relat_1(B_422) ) ),
    inference(resolution,[status(thm)],[c_8478,c_8788])).

tff(c_17123,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_17109,c_8799])).

tff(c_17143,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8448,c_17123])).

tff(c_17145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7590,c_17143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:05:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.42/3.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.42/3.64  
% 9.42/3.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.42/3.64  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.42/3.64  
% 9.42/3.64  %Foreground sorts:
% 9.42/3.64  
% 9.42/3.64  
% 9.42/3.64  %Background operators:
% 9.42/3.64  
% 9.42/3.64  
% 9.42/3.64  %Foreground operators:
% 9.42/3.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.42/3.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.42/3.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.42/3.64  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.42/3.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.42/3.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.42/3.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.42/3.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.42/3.64  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.42/3.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.42/3.64  tff('#skF_2', type, '#skF_2': $i).
% 9.42/3.64  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.42/3.64  tff('#skF_3', type, '#skF_3': $i).
% 9.42/3.64  tff('#skF_1', type, '#skF_1': $i).
% 9.42/3.64  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.42/3.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.42/3.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.42/3.64  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.42/3.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.42/3.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.42/3.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.42/3.64  tff('#skF_4', type, '#skF_4': $i).
% 9.42/3.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.42/3.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.42/3.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.42/3.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.42/3.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.42/3.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.42/3.64  
% 9.42/3.67  tff(f_190, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.42/3.67  tff(f_128, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 9.42/3.67  tff(f_232, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 9.42/3.67  tff(f_188, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.42/3.67  tff(f_166, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.42/3.67  tff(f_170, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.42/3.67  tff(f_146, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.42/3.67  tff(f_100, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.42/3.67  tff(f_126, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 9.42/3.67  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 9.42/3.67  tff(f_212, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 9.42/3.67  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.42/3.67  tff(f_178, axiom, (![A]: (~v1_xboole_0(A) => (~v1_xboole_0(k6_relat_1(A)) & v1_relat_1(k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_relset_1)).
% 9.42/3.67  tff(f_48, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 9.42/3.67  tff(f_116, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 9.42/3.67  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 9.42/3.67  tff(f_59, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 9.42/3.67  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.42/3.67  tff(f_138, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.42/3.67  tff(f_88, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 9.42/3.67  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 9.42/3.67  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.42/3.67  tff(f_154, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 9.42/3.67  tff(c_88, plain, (![A_54]: (k6_relat_1(A_54)=k6_partfun1(A_54))), inference(cnfTransformation, [status(thm)], [f_190])).
% 9.42/3.67  tff(c_58, plain, (![A_27]: (v2_funct_1(k6_relat_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.42/3.67  tff(c_111, plain, (![A_27]: (v2_funct_1(k6_partfun1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_58])).
% 9.42/3.67  tff(c_108, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_232])).
% 9.42/3.67  tff(c_104, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_232])).
% 9.42/3.67  tff(c_102, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_232])).
% 9.42/3.67  tff(c_98, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_232])).
% 9.42/3.67  tff(c_2252, plain, (![E_206, B_203, F_201, C_205, A_204, D_202]: (k1_partfun1(A_204, B_203, C_205, D_202, E_206, F_201)=k5_relat_1(E_206, F_201) | ~m1_subset_1(F_201, k1_zfmisc_1(k2_zfmisc_1(C_205, D_202))) | ~v1_funct_1(F_201) | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))) | ~v1_funct_1(E_206))), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.42/3.67  tff(c_2262, plain, (![A_204, B_203, E_206]: (k1_partfun1(A_204, B_203, '#skF_2', '#skF_1', E_206, '#skF_4')=k5_relat_1(E_206, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_203))) | ~v1_funct_1(E_206))), inference(resolution, [status(thm)], [c_98, c_2252])).
% 9.42/3.67  tff(c_4434, plain, (![A_285, B_286, E_287]: (k1_partfun1(A_285, B_286, '#skF_2', '#skF_1', E_287, '#skF_4')=k5_relat_1(E_287, '#skF_4') | ~m1_subset_1(E_287, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))) | ~v1_funct_1(E_287))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_2262])).
% 9.42/3.67  tff(c_4470, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_4434])).
% 9.42/3.67  tff(c_4478, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_4470])).
% 9.42/3.67  tff(c_74, plain, (![E_44, C_42, F_45, A_40, D_43, B_41]: (m1_subset_1(k1_partfun1(A_40, B_41, C_42, D_43, E_44, F_45), k1_zfmisc_1(k2_zfmisc_1(A_40, D_43))) | ~m1_subset_1(F_45, k1_zfmisc_1(k2_zfmisc_1(C_42, D_43))) | ~v1_funct_1(F_45) | ~m1_subset_1(E_44, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_1(E_44))), inference(cnfTransformation, [status(thm)], [f_166])).
% 9.42/3.67  tff(c_5678, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4478, c_74])).
% 9.42/3.67  tff(c_5685, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_104, c_102, c_98, c_5678])).
% 9.42/3.67  tff(c_80, plain, (![A_46]: (m1_subset_1(k6_partfun1(A_46), k1_zfmisc_1(k2_zfmisc_1(A_46, A_46))))), inference(cnfTransformation, [status(thm)], [f_170])).
% 9.42/3.67  tff(c_96, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_232])).
% 9.42/3.67  tff(c_1503, plain, (![D_172, C_173, A_174, B_175]: (D_172=C_173 | ~r2_relset_1(A_174, B_175, C_173, D_172) | ~m1_subset_1(D_172, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.42/3.67  tff(c_1509, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_96, c_1503])).
% 9.42/3.67  tff(c_1520, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1509])).
% 9.42/3.67  tff(c_7390, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5685, c_4478, c_4478, c_1520])).
% 9.42/3.67  tff(c_94, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_232])).
% 9.42/3.67  tff(c_164, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_94])).
% 9.42/3.67  tff(c_38, plain, (![A_22]: (k2_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.42/3.67  tff(c_118, plain, (![A_22]: (k2_relat_1(k6_partfun1(A_22))=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_38])).
% 9.42/3.67  tff(c_54, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.42/3.67  tff(c_113, plain, (![A_26]: (v1_relat_1(k6_partfun1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_54])).
% 9.42/3.67  tff(c_416, plain, (![A_99]: (k2_relat_1(A_99)!=k1_xboole_0 | k1_xboole_0=A_99 | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.42/3.67  tff(c_428, plain, (![A_26]: (k2_relat_1(k6_partfun1(A_26))!=k1_xboole_0 | k6_partfun1(A_26)=k1_xboole_0)), inference(resolution, [status(thm)], [c_113, c_416])).
% 9.42/3.67  tff(c_465, plain, (![A_101]: (k1_xboole_0!=A_101 | k6_partfun1(A_101)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_428])).
% 9.42/3.67  tff(c_477, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_465, c_96])).
% 9.42/3.67  tff(c_571, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_477])).
% 9.42/3.67  tff(c_106, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_232])).
% 9.42/3.67  tff(c_100, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_232])).
% 9.42/3.67  tff(c_92, plain, (![B_56, C_57, A_55, E_60, D_58]: (k1_xboole_0=C_57 | v2_funct_1(D_58) | ~v2_funct_1(k1_partfun1(A_55, B_56, B_56, C_57, D_58, E_60)) | ~m1_subset_1(E_60, k1_zfmisc_1(k2_zfmisc_1(B_56, C_57))) | ~v1_funct_2(E_60, B_56, C_57) | ~v1_funct_1(E_60) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))) | ~v1_funct_2(D_58, A_55, B_56) | ~v1_funct_1(D_58))), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.42/3.67  tff(c_5675, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4478, c_92])).
% 9.42/3.67  tff(c_5682, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_104, c_102, c_100, c_98, c_5675])).
% 9.42/3.67  tff(c_5683, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_164, c_571, c_5682])).
% 9.42/3.67  tff(c_7396, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7390, c_5683])).
% 9.42/3.67  tff(c_7406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_7396])).
% 9.42/3.67  tff(c_7408, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_477])).
% 9.42/3.67  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.42/3.67  tff(c_84, plain, (![A_47]: (~v1_xboole_0(k6_relat_1(A_47)) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_178])).
% 9.42/3.67  tff(c_109, plain, (![A_47]: (~v1_xboole_0(k6_partfun1(A_47)) | v1_xboole_0(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84])).
% 9.42/3.67  tff(c_480, plain, (![A_101]: (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(A_101) | k1_xboole_0!=A_101)), inference(superposition, [status(thm), theory('equality')], [c_465, c_109])).
% 9.42/3.67  tff(c_506, plain, (![A_101]: (v1_xboole_0(A_101) | k1_xboole_0!=A_101)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_480])).
% 9.42/3.67  tff(c_7456, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7408, c_506])).
% 9.42/3.67  tff(c_14, plain, (![A_7, B_8]: (v1_xboole_0(k2_zfmisc_1(A_7, B_8)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.42/3.67  tff(c_7543, plain, (![A_356]: (v2_funct_1(A_356) | ~v1_funct_1(A_356) | ~v1_relat_1(A_356) | ~v1_xboole_0(A_356))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.42/3.67  tff(c_7546, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_7543, c_164])).
% 9.42/3.67  tff(c_7549, plain, (~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_7546])).
% 9.42/3.67  tff(c_7550, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_7549])).
% 9.42/3.67  tff(c_7432, plain, (![B_352, A_353]: (v1_xboole_0(B_352) | ~m1_subset_1(B_352, k1_zfmisc_1(A_353)) | ~v1_xboole_0(A_353))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.42/3.67  tff(c_7444, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_104, c_7432])).
% 9.42/3.67  tff(c_7555, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_7550, c_7444])).
% 9.42/3.67  tff(c_7564, plain, (~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_14, c_7555])).
% 9.42/3.67  tff(c_7570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7456, c_7564])).
% 9.42/3.67  tff(c_7571, plain, (~v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_7549])).
% 9.42/3.67  tff(c_7572, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_7549])).
% 9.42/3.67  tff(c_18, plain, (![A_12]: (v1_relat_1(A_12) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.42/3.67  tff(c_7580, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7572, c_18])).
% 9.42/3.67  tff(c_7589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7571, c_7580])).
% 9.42/3.67  tff(c_7590, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_94])).
% 9.42/3.67  tff(c_8431, plain, (![C_419, A_420, B_421]: (v1_relat_1(C_419) | ~m1_subset_1(C_419, k1_zfmisc_1(k2_zfmisc_1(A_420, B_421))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.42/3.67  tff(c_8448, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_98, c_8431])).
% 9.42/3.67  tff(c_8726, plain, (![C_436, B_437, A_438]: (v5_relat_1(C_436, B_437) | ~m1_subset_1(C_436, k1_zfmisc_1(k2_zfmisc_1(A_438, B_437))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.42/3.67  tff(c_8745, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_98, c_8726])).
% 9.42/3.67  tff(c_8447, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_8431])).
% 9.42/3.67  tff(c_10026, plain, (![C_503, D_500, B_501, A_502, F_499, E_504]: (k1_partfun1(A_502, B_501, C_503, D_500, E_504, F_499)=k5_relat_1(E_504, F_499) | ~m1_subset_1(F_499, k1_zfmisc_1(k2_zfmisc_1(C_503, D_500))) | ~v1_funct_1(F_499) | ~m1_subset_1(E_504, k1_zfmisc_1(k2_zfmisc_1(A_502, B_501))) | ~v1_funct_1(E_504))), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.42/3.67  tff(c_10042, plain, (![A_502, B_501, E_504]: (k1_partfun1(A_502, B_501, '#skF_2', '#skF_1', E_504, '#skF_4')=k5_relat_1(E_504, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_504, k1_zfmisc_1(k2_zfmisc_1(A_502, B_501))) | ~v1_funct_1(E_504))), inference(resolution, [status(thm)], [c_98, c_10026])).
% 9.42/3.67  tff(c_12301, plain, (![A_583, B_584, E_585]: (k1_partfun1(A_583, B_584, '#skF_2', '#skF_1', E_585, '#skF_4')=k5_relat_1(E_585, '#skF_4') | ~m1_subset_1(E_585, k1_zfmisc_1(k2_zfmisc_1(A_583, B_584))) | ~v1_funct_1(E_585))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_10042])).
% 9.42/3.67  tff(c_12334, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_12301])).
% 9.42/3.67  tff(c_12342, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_12334])).
% 9.42/3.67  tff(c_9238, plain, (![D_466, C_467, A_468, B_469]: (D_466=C_467 | ~r2_relset_1(A_468, B_469, C_467, D_466) | ~m1_subset_1(D_466, k1_zfmisc_1(k2_zfmisc_1(A_468, B_469))) | ~m1_subset_1(C_467, k1_zfmisc_1(k2_zfmisc_1(A_468, B_469))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.42/3.67  tff(c_9246, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_96, c_9238])).
% 9.42/3.67  tff(c_9261, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_9246])).
% 9.42/3.67  tff(c_9382, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_9261])).
% 9.42/3.67  tff(c_13023, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_12342, c_9382])).
% 9.42/3.67  tff(c_12833, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12342, c_74])).
% 9.42/3.67  tff(c_12840, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_104, c_102, c_98, c_12833])).
% 9.42/3.67  tff(c_13552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13023, c_12840])).
% 9.42/3.67  tff(c_13553, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_9261])).
% 9.42/3.67  tff(c_14096, plain, (![A_645, B_644, D_643, F_642, E_647, C_646]: (k1_partfun1(A_645, B_644, C_646, D_643, E_647, F_642)=k5_relat_1(E_647, F_642) | ~m1_subset_1(F_642, k1_zfmisc_1(k2_zfmisc_1(C_646, D_643))) | ~v1_funct_1(F_642) | ~m1_subset_1(E_647, k1_zfmisc_1(k2_zfmisc_1(A_645, B_644))) | ~v1_funct_1(E_647))), inference(cnfTransformation, [status(thm)], [f_188])).
% 9.42/3.67  tff(c_14110, plain, (![A_645, B_644, E_647]: (k1_partfun1(A_645, B_644, '#skF_2', '#skF_1', E_647, '#skF_4')=k5_relat_1(E_647, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_647, k1_zfmisc_1(k2_zfmisc_1(A_645, B_644))) | ~v1_funct_1(E_647))), inference(resolution, [status(thm)], [c_98, c_14096])).
% 9.42/3.67  tff(c_17007, plain, (![A_741, B_742, E_743]: (k1_partfun1(A_741, B_742, '#skF_2', '#skF_1', E_743, '#skF_4')=k5_relat_1(E_743, '#skF_4') | ~m1_subset_1(E_743, k1_zfmisc_1(k2_zfmisc_1(A_741, B_742))) | ~v1_funct_1(E_743))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_14110])).
% 9.42/3.67  tff(c_17043, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_17007])).
% 9.42/3.67  tff(c_17054, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_13553, c_17043])).
% 9.42/3.67  tff(c_30, plain, (![A_18, B_20]: (r1_tarski(k2_relat_1(k5_relat_1(A_18, B_20)), k2_relat_1(B_20)) | ~v1_relat_1(B_20) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.42/3.67  tff(c_17070, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_17054, c_30])).
% 9.42/3.67  tff(c_17090, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8447, c_8448, c_118, c_17070])).
% 9.42/3.67  tff(c_8486, plain, (![B_425, A_426]: (r1_tarski(k2_relat_1(B_425), A_426) | ~v5_relat_1(B_425, A_426) | ~v1_relat_1(B_425))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.42/3.67  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.42/3.67  tff(c_8496, plain, (![B_425, A_426]: (k2_relat_1(B_425)=A_426 | ~r1_tarski(A_426, k2_relat_1(B_425)) | ~v5_relat_1(B_425, A_426) | ~v1_relat_1(B_425))), inference(resolution, [status(thm)], [c_8486, c_4])).
% 9.42/3.67  tff(c_17104, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_17090, c_8496])).
% 9.42/3.67  tff(c_17109, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8448, c_8745, c_17104])).
% 9.42/3.67  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.42/3.67  tff(c_8468, plain, (![B_422, A_423]: (v5_relat_1(B_422, A_423) | ~r1_tarski(k2_relat_1(B_422), A_423) | ~v1_relat_1(B_422))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.42/3.67  tff(c_8478, plain, (![B_422]: (v5_relat_1(B_422, k2_relat_1(B_422)) | ~v1_relat_1(B_422))), inference(resolution, [status(thm)], [c_8, c_8468])).
% 9.42/3.67  tff(c_8788, plain, (![B_442]: (v2_funct_2(B_442, k2_relat_1(B_442)) | ~v5_relat_1(B_442, k2_relat_1(B_442)) | ~v1_relat_1(B_442))), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.42/3.67  tff(c_8799, plain, (![B_422]: (v2_funct_2(B_422, k2_relat_1(B_422)) | ~v1_relat_1(B_422))), inference(resolution, [status(thm)], [c_8478, c_8788])).
% 9.42/3.67  tff(c_17123, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_17109, c_8799])).
% 9.42/3.67  tff(c_17143, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8448, c_17123])).
% 9.42/3.67  tff(c_17145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7590, c_17143])).
% 9.42/3.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.42/3.67  
% 9.42/3.67  Inference rules
% 9.42/3.67  ----------------------
% 9.42/3.67  #Ref     : 10
% 9.42/3.67  #Sup     : 4198
% 9.42/3.67  #Fact    : 0
% 9.42/3.67  #Define  : 0
% 9.42/3.67  #Split   : 31
% 9.42/3.67  #Chain   : 0
% 9.42/3.67  #Close   : 0
% 9.42/3.67  
% 9.42/3.67  Ordering : KBO
% 9.42/3.67  
% 9.42/3.67  Simplification rules
% 9.42/3.67  ----------------------
% 9.42/3.67  #Subsume      : 602
% 9.42/3.67  #Demod        : 2835
% 9.42/3.67  #Tautology    : 2232
% 9.42/3.67  #SimpNegUnit  : 20
% 9.42/3.67  #BackRed      : 47
% 9.42/3.67  
% 9.42/3.67  #Partial instantiations: 0
% 9.42/3.67  #Strategies tried      : 1
% 9.42/3.67  
% 9.42/3.67  Timing (in seconds)
% 9.42/3.67  ----------------------
% 9.78/3.67  Preprocessing        : 0.37
% 9.78/3.67  Parsing              : 0.19
% 9.78/3.67  CNF conversion       : 0.03
% 9.78/3.67  Main loop            : 2.48
% 9.78/3.67  Inferencing          : 0.65
% 9.78/3.67  Reduction            : 0.94
% 9.78/3.67  Demodulation         : 0.68
% 9.78/3.67  BG Simplification    : 0.07
% 9.78/3.67  Subsumption          : 0.65
% 9.78/3.67  Abstraction          : 0.09
% 9.78/3.67  MUC search           : 0.00
% 9.78/3.67  Cooper               : 0.00
% 9.78/3.67  Total                : 2.90
% 9.78/3.67  Index Insertion      : 0.00
% 9.78/3.67  Index Deletion       : 0.00
% 9.78/3.67  Index Matching       : 0.00
% 9.78/3.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
