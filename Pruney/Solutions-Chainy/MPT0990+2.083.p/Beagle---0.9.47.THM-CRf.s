%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:08 EST 2020

% Result     : Theorem 46.53s
% Output     : CNFRefutation 46.60s
% Verified   : 
% Statistics : Number of formulae       :  191 (2234 expanded)
%              Number of leaves         :   44 ( 795 expanded)
%              Depth                    :   22
%              Number of atoms          :  484 (9017 expanded)
%              Number of equality atoms :  171 (3216 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_204,negated_conjecture,(
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

tff(f_117,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_119,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_95,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_40,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_178,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_162,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_524,plain,(
    ! [A_121,F_120,E_122,D_123,B_119,C_118] :
      ( k1_partfun1(A_121,B_119,C_118,D_123,E_122,F_120) = k5_relat_1(E_122,F_120)
      | ~ m1_subset_1(F_120,k1_zfmisc_1(k2_zfmisc_1(C_118,D_123)))
      | ~ v1_funct_1(F_120)
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_121,B_119)))
      | ~ v1_funct_1(E_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_530,plain,(
    ! [A_121,B_119,E_122] :
      ( k1_partfun1(A_121,B_119,'#skF_2','#skF_1',E_122,'#skF_4') = k5_relat_1(E_122,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_122,k1_zfmisc_1(k2_zfmisc_1(A_121,B_119)))
      | ~ v1_funct_1(E_122) ) ),
    inference(resolution,[status(thm)],[c_66,c_524])).

tff(c_689,plain,(
    ! [A_138,B_139,E_140] :
      ( k1_partfun1(A_138,B_139,'#skF_2','#skF_1',E_140,'#skF_4') = k5_relat_1(E_140,'#skF_4')
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_1(E_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_530])).

tff(c_695,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_689])).

tff(c_702,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_695])).

tff(c_38,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_30,plain,(
    ! [A_23] : m1_subset_1(k6_relat_1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_77,plain,(
    ! [A_23] : m1_subset_1(k6_partfun1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_302,plain,(
    ! [D_83,C_84,A_85,B_86] :
      ( D_83 = C_84
      | ~ r2_relset_1(A_85,B_86,C_84,D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_310,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_62,c_302])).

tff(c_325,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_310])).

tff(c_388,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_325])).

tff(c_707,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_388])).

tff(c_723,plain,(
    ! [E_143,A_145,C_141,B_142,D_146,F_144] :
      ( m1_subset_1(k1_partfun1(A_145,B_142,C_141,D_146,E_143,F_144),k1_zfmisc_1(k2_zfmisc_1(A_145,D_146)))
      | ~ m1_subset_1(F_144,k1_zfmisc_1(k2_zfmisc_1(C_141,D_146)))
      | ~ v1_funct_1(F_144)
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(A_145,B_142)))
      | ~ v1_funct_1(E_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_759,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_723])).

tff(c_781,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_759])).

tff(c_783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_707,c_781])).

tff(c_784,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_1204,plain,(
    ! [E_199,C_197,D_202,B_198,A_201,F_200] :
      ( v1_funct_1(k1_partfun1(A_201,B_198,C_197,D_202,E_199,F_200))
      | ~ m1_subset_1(F_200,k1_zfmisc_1(k2_zfmisc_1(C_197,D_202)))
      | ~ v1_funct_1(F_200)
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(A_201,B_198)))
      | ~ v1_funct_1(E_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1210,plain,(
    ! [A_201,B_198,E_199] :
      ( v1_funct_1(k1_partfun1(A_201,B_198,'#skF_2','#skF_1',E_199,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(A_201,B_198)))
      | ~ v1_funct_1(E_199) ) ),
    inference(resolution,[status(thm)],[c_66,c_1204])).

tff(c_1236,plain,(
    ! [A_207,B_208,E_209] :
      ( v1_funct_1(k1_partfun1(A_207,B_208,'#skF_2','#skF_1',E_209,'#skF_4'))
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ v1_funct_1(E_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1210])).

tff(c_1242,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1236])).

tff(c_1249,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_784,c_1242])).

tff(c_8,plain,(
    ! [A_5] : k2_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_81,plain,(
    ! [A_5] : k2_relat_1(k6_partfun1(A_5)) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8])).

tff(c_14,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_80,plain,(
    ! [A_7] : v1_relat_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_14])).

tff(c_142,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_154,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_142])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_196,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_202,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_196])).

tff(c_209,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_202])).

tff(c_20,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_relat_1(k2_relat_1(A_10)) != k5_relat_1(B_12,A_10)
      | k2_relat_1(B_12) != k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1151,plain,(
    ! [A_194,B_195] :
      ( k2_funct_1(A_194) = B_195
      | k6_partfun1(k2_relat_1(A_194)) != k5_relat_1(B_195,A_194)
      | k2_relat_1(B_195) != k1_relat_1(A_194)
      | ~ v2_funct_1(A_194)
      | ~ v1_funct_1(B_195)
      | ~ v1_relat_1(B_195)
      | ~ v1_funct_1(A_194)
      | ~ v1_relat_1(A_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_20])).

tff(c_1161,plain,(
    ! [B_195] :
      ( k2_funct_1('#skF_3') = B_195
      | k5_relat_1(B_195,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_195) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_195)
      | ~ v1_relat_1(B_195)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_1151])).

tff(c_1170,plain,(
    ! [B_196] :
      ( k2_funct_1('#skF_3') = B_196
      | k5_relat_1(B_196,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_196) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_196)
      | ~ v1_relat_1(B_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_76,c_60,c_1161])).

tff(c_1188,plain,(
    ! [A_7] :
      ( k6_partfun1(A_7) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_7),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_7)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_80,c_1170])).

tff(c_1269,plain,(
    ! [A_217] :
      ( k6_partfun1(A_217) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_217),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_217
      | ~ v1_funct_1(k6_partfun1(A_217)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1188])).

tff(c_1273,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_1249,c_1269])).

tff(c_1274,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1273])).

tff(c_12,plain,(
    ! [A_6] :
      ( v1_relat_1(k2_funct_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_4] :
      ( k10_relat_1(A_4,k2_relat_1(A_4)) = k1_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_217,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_4])).

tff(c_223,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_217])).

tff(c_18,plain,(
    ! [B_9,A_8] :
      ( k9_relat_1(k2_funct_1(B_9),A_8) = k10_relat_1(B_9,A_8)
      | ~ v2_funct_1(B_9)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( k9_relat_1(B_3,k2_relat_1(A_1)) = k2_relat_1(k5_relat_1(A_1,B_3))
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_214,plain,(
    ! [B_3] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_3)) = k9_relat_1(B_3,'#skF_2')
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_2])).

tff(c_259,plain,(
    ! [B_79] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_79)) = k9_relat_1(B_79,'#skF_2')
      | ~ v1_relat_1(B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_214])).

tff(c_274,plain,(
    ! [B_80] :
      ( k10_relat_1(k5_relat_1('#skF_3',B_80),k9_relat_1(B_80,'#skF_2')) = k1_relat_1(k5_relat_1('#skF_3',B_80))
      | ~ v1_relat_1(k5_relat_1('#skF_3',B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_4])).

tff(c_816,plain,(
    ! [B_150] :
      ( k10_relat_1(k5_relat_1('#skF_3',k2_funct_1(B_150)),k10_relat_1(B_150,'#skF_2')) = k1_relat_1(k5_relat_1('#skF_3',k2_funct_1(B_150)))
      | ~ v1_relat_1(k5_relat_1('#skF_3',k2_funct_1(B_150)))
      | ~ v1_relat_1(k2_funct_1(B_150))
      | ~ v2_funct_1(B_150)
      | ~ v1_funct_1(B_150)
      | ~ v1_relat_1(B_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_274])).

tff(c_825,plain,
    ( k10_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k1_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_816])).

tff(c_833,plain,
    ( k10_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k1_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_76,c_60,c_825])).

tff(c_836,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_833])).

tff(c_839,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_836])).

tff(c_843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_76,c_839])).

tff(c_845,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_833])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_1400,plain,(
    ! [A_228,C_229,B_230] :
      ( k6_partfun1(A_228) = k5_relat_1(C_229,k2_funct_1(C_229))
      | k1_xboole_0 = B_230
      | ~ v2_funct_1(C_229)
      | k2_relset_1(A_228,B_230,C_229) != B_230
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_228,B_230)))
      | ~ v1_funct_2(C_229,A_228,B_230)
      | ~ v1_funct_1(C_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1404,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1400])).

tff(c_1412,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_64,c_60,c_1404])).

tff(c_1413,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1412])).

tff(c_238,plain,(
    ! [B_77,A_78] :
      ( k9_relat_1(k2_funct_1(B_77),A_78) = k10_relat_1(B_77,A_78)
      | ~ v2_funct_1(B_77)
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_245,plain,(
    ! [A_1,B_77] :
      ( k2_relat_1(k5_relat_1(A_1,k2_funct_1(B_77))) = k10_relat_1(B_77,k2_relat_1(A_1))
      | ~ v1_relat_1(k2_funct_1(B_77))
      | ~ v1_relat_1(A_1)
      | ~ v2_funct_1(B_77)
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_2])).

tff(c_1431,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_relat_1(k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1413,c_245])).

tff(c_1448,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_76,c_60,c_154,c_845,c_81,c_223,c_209,c_1431])).

tff(c_1450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1274,c_1448])).

tff(c_1452,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1273])).

tff(c_54,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_155,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_142])).

tff(c_1179,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_155,c_1170])).

tff(c_1194,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1179])).

tff(c_1195,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1194])).

tff(c_1202,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1195])).

tff(c_1455,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1452,c_1202])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_156,plain,(
    ! [A_65,B_66,D_67] :
      ( r2_relset_1(A_65,B_66,D_67,D_67)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_163,plain,(
    ! [A_23] : r2_relset_1(A_23,A_23,k6_partfun1(A_23),k6_partfun1(A_23)) ),
    inference(resolution,[status(thm)],[c_77,c_156])).

tff(c_210,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_196])).

tff(c_2023,plain,(
    ! [A_258,B_259,C_260,D_261] :
      ( k2_relset_1(A_258,B_259,C_260) = B_259
      | ~ r2_relset_1(B_259,B_259,k1_partfun1(B_259,A_258,A_258,B_259,D_261,C_260),k6_partfun1(B_259))
      | ~ m1_subset_1(D_261,k1_zfmisc_1(k2_zfmisc_1(B_259,A_258)))
      | ~ v1_funct_2(D_261,B_259,A_258)
      | ~ v1_funct_1(D_261)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259)))
      | ~ v1_funct_2(C_260,A_258,B_259)
      | ~ v1_funct_1(C_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2029,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_2023])).

tff(c_2033,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_163,c_210,c_2029])).

tff(c_2035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1455,c_2033])).

tff(c_2036,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1195])).

tff(c_2454,plain,(
    ! [B_301,A_303,D_305,C_300,F_302,E_304] :
      ( k1_partfun1(A_303,B_301,C_300,D_305,E_304,F_302) = k5_relat_1(E_304,F_302)
      | ~ m1_subset_1(F_302,k1_zfmisc_1(k2_zfmisc_1(C_300,D_305)))
      | ~ v1_funct_1(F_302)
      | ~ m1_subset_1(E_304,k1_zfmisc_1(k2_zfmisc_1(A_303,B_301)))
      | ~ v1_funct_1(E_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2460,plain,(
    ! [A_303,B_301,E_304] :
      ( k1_partfun1(A_303,B_301,'#skF_2','#skF_1',E_304,'#skF_4') = k5_relat_1(E_304,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_304,k1_zfmisc_1(k2_zfmisc_1(A_303,B_301)))
      | ~ v1_funct_1(E_304) ) ),
    inference(resolution,[status(thm)],[c_66,c_2454])).

tff(c_3161,plain,(
    ! [A_345,B_346,E_347] :
      ( k1_partfun1(A_345,B_346,'#skF_2','#skF_1',E_347,'#skF_4') = k5_relat_1(E_347,'#skF_4')
      | ~ m1_subset_1(E_347,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346)))
      | ~ v1_funct_1(E_347) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2460])).

tff(c_3167,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_3161])).

tff(c_3174,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_784,c_3167])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_2115,plain,(
    ! [E_267,A_269,B_266,F_268,D_270,C_265] :
      ( v1_funct_1(k1_partfun1(A_269,B_266,C_265,D_270,E_267,F_268))
      | ~ m1_subset_1(F_268,k1_zfmisc_1(k2_zfmisc_1(C_265,D_270)))
      | ~ v1_funct_1(F_268)
      | ~ m1_subset_1(E_267,k1_zfmisc_1(k2_zfmisc_1(A_269,B_266)))
      | ~ v1_funct_1(E_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2121,plain,(
    ! [A_269,B_266,E_267] :
      ( v1_funct_1(k1_partfun1(A_269,B_266,'#skF_2','#skF_1',E_267,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_267,k1_zfmisc_1(k2_zfmisc_1(A_269,B_266)))
      | ~ v1_funct_1(E_267) ) ),
    inference(resolution,[status(thm)],[c_66,c_2115])).

tff(c_2146,plain,(
    ! [A_274,B_275,E_276] :
      ( v1_funct_1(k1_partfun1(A_274,B_275,'#skF_2','#skF_1',E_276,'#skF_4'))
      | ~ m1_subset_1(E_276,k1_zfmisc_1(k2_zfmisc_1(A_274,B_275)))
      | ~ v1_funct_1(E_276) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2121])).

tff(c_2152,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_2146])).

tff(c_2159,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_784,c_2152])).

tff(c_1201,plain,(
    ! [A_7] :
      ( k6_partfun1(A_7) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_7),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_7
      | ~ v1_funct_1(k6_partfun1(A_7)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1188])).

tff(c_2166,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_2159,c_1201])).

tff(c_2169,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2166])).

tff(c_2322,plain,(
    ! [A_296,C_297,B_298] :
      ( k6_partfun1(A_296) = k5_relat_1(C_297,k2_funct_1(C_297))
      | k1_xboole_0 = B_298
      | ~ v2_funct_1(C_297)
      | k2_relset_1(A_296,B_298,C_297) != B_298
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_296,B_298)))
      | ~ v1_funct_2(C_297,A_296,B_298)
      | ~ v1_funct_1(C_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_2326,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_2322])).

tff(c_2334,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_64,c_60,c_2326])).

tff(c_2335,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2334])).

tff(c_2353,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k2_relat_1(k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2335,c_245])).

tff(c_2370,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_76,c_60,c_154,c_845,c_81,c_223,c_209,c_2353])).

tff(c_2372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2169,c_2370])).

tff(c_2374,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2166])).

tff(c_2037,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1195])).

tff(c_2038,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2037,c_210])).

tff(c_2380,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2374,c_2038])).

tff(c_2500,plain,(
    ! [A_309,C_310,B_311] :
      ( k6_partfun1(A_309) = k5_relat_1(C_310,k2_funct_1(C_310))
      | k1_xboole_0 = B_311
      | ~ v2_funct_1(C_310)
      | k2_relset_1(A_309,B_311,C_310) != B_311
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(A_309,B_311)))
      | ~ v1_funct_2(C_310,A_309,B_311)
      | ~ v1_funct_1(C_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_2506,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_2500])).

tff(c_2516,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_2380,c_2506])).

tff(c_2517,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2516])).

tff(c_2585,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2517])).

tff(c_16,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_79,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_16])).

tff(c_3035,plain,(
    ! [C_338,A_336,E_337,D_334,B_335] :
      ( k1_xboole_0 = C_338
      | v2_funct_1(E_337)
      | k2_relset_1(A_336,B_335,D_334) != B_335
      | ~ v2_funct_1(k1_partfun1(A_336,B_335,B_335,C_338,D_334,E_337))
      | ~ m1_subset_1(E_337,k1_zfmisc_1(k2_zfmisc_1(B_335,C_338)))
      | ~ v1_funct_2(E_337,B_335,C_338)
      | ~ v1_funct_1(E_337)
      | ~ m1_subset_1(D_334,k1_zfmisc_1(k2_zfmisc_1(A_336,B_335)))
      | ~ v1_funct_2(D_334,A_336,B_335)
      | ~ v1_funct_1(D_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_3041,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_3035])).

tff(c_3049,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_66,c_79,c_64,c_3041])).

tff(c_3051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2585,c_58,c_3049])).

tff(c_3053,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2517])).

tff(c_2047,plain,
    ( k10_relat_1('#skF_4',k1_relat_1('#skF_3')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2037,c_4])).

tff(c_2055,plain,(
    k10_relat_1('#skF_4',k1_relat_1('#skF_3')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_2047])).

tff(c_2378,plain,(
    k10_relat_1('#skF_4','#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2374,c_2055])).

tff(c_2381,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2374,c_2037])).

tff(c_3052,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2517])).

tff(c_3060,plain,
    ( k10_relat_1('#skF_4',k2_relat_1('#skF_4')) = k2_relat_1(k6_partfun1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3052,c_245])).

tff(c_3065,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_70,c_3053,c_155,c_81,c_2378,c_2381,c_3060])).

tff(c_3067,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3065])).

tff(c_3087,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_3067])).

tff(c_3091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_70,c_3087])).

tff(c_3092,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3065])).

tff(c_78,plain,(
    ! [A_10,B_12] :
      ( k2_funct_1(A_10) = B_12
      | k6_partfun1(k2_relat_1(A_10)) != k5_relat_1(B_12,A_10)
      | k2_relat_1(B_12) != k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_20])).

tff(c_2041,plain,(
    ! [B_12] :
      ( k2_funct_1('#skF_4') = B_12
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_12,'#skF_4')
      | k2_relat_1(B_12) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2037,c_78])).

tff(c_2051,plain,(
    ! [B_12] :
      ( k2_funct_1('#skF_4') = B_12
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_12,'#skF_4')
      | k2_relat_1(B_12) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_70,c_2041])).

tff(c_49492,plain,(
    ! [B_1215] :
      ( k2_funct_1('#skF_4') = B_1215
      | k5_relat_1(B_1215,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_1215) != '#skF_2'
      | ~ v1_funct_1(B_1215)
      | ~ v1_relat_1(B_1215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3053,c_3092,c_2374,c_2051])).

tff(c_50386,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_154,c_49492])).

tff(c_51139,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_209,c_3174,c_50386])).

tff(c_51149,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51139,c_3052])).

tff(c_51154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2036,c_51149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 46.53/35.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 46.60/35.57  
% 46.60/35.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 46.60/35.57  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 46.60/35.57  
% 46.60/35.57  %Foreground sorts:
% 46.60/35.57  
% 46.60/35.57  
% 46.60/35.57  %Background operators:
% 46.60/35.57  
% 46.60/35.57  
% 46.60/35.57  %Foreground operators:
% 46.60/35.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 46.60/35.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 46.60/35.57  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 46.60/35.57  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 46.60/35.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 46.60/35.57  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 46.60/35.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 46.60/35.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 46.60/35.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 46.60/35.57  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 46.60/35.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 46.60/35.57  tff('#skF_2', type, '#skF_2': $i).
% 46.60/35.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 46.60/35.57  tff('#skF_3', type, '#skF_3': $i).
% 46.60/35.57  tff('#skF_1', type, '#skF_1': $i).
% 46.60/35.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 46.60/35.57  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 46.60/35.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 46.60/35.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 46.60/35.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 46.60/35.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 46.60/35.57  tff('#skF_4', type, '#skF_4': $i).
% 46.60/35.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 46.60/35.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 46.60/35.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 46.60/35.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 46.60/35.57  
% 46.60/35.60  tff(f_204, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 46.60/35.60  tff(f_117, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 46.60/35.60  tff(f_119, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 46.60/35.60  tff(f_95, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 46.60/35.60  tff(f_93, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 46.60/35.60  tff(f_107, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 46.60/35.60  tff(f_40, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 46.60/35.60  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 46.60/35.60  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 46.60/35.60  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 46.60/35.60  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 46.60/35.60  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 46.60/35.60  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 46.60/35.60  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 46.60/35.60  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 46.60/35.60  tff(f_178, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 46.60/35.60  tff(f_136, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 46.60/35.60  tff(f_162, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 46.60/35.60  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 46.60/35.60  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 46.60/35.60  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_204])).
% 46.60/35.60  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 46.60/35.60  tff(c_524, plain, (![A_121, F_120, E_122, D_123, B_119, C_118]: (k1_partfun1(A_121, B_119, C_118, D_123, E_122, F_120)=k5_relat_1(E_122, F_120) | ~m1_subset_1(F_120, k1_zfmisc_1(k2_zfmisc_1(C_118, D_123))) | ~v1_funct_1(F_120) | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_121, B_119))) | ~v1_funct_1(E_122))), inference(cnfTransformation, [status(thm)], [f_117])).
% 46.60/35.60  tff(c_530, plain, (![A_121, B_119, E_122]: (k1_partfun1(A_121, B_119, '#skF_2', '#skF_1', E_122, '#skF_4')=k5_relat_1(E_122, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_122, k1_zfmisc_1(k2_zfmisc_1(A_121, B_119))) | ~v1_funct_1(E_122))), inference(resolution, [status(thm)], [c_66, c_524])).
% 46.60/35.60  tff(c_689, plain, (![A_138, B_139, E_140]: (k1_partfun1(A_138, B_139, '#skF_2', '#skF_1', E_140, '#skF_4')=k5_relat_1(E_140, '#skF_4') | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_1(E_140))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_530])).
% 46.60/35.60  tff(c_695, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_689])).
% 46.60/35.60  tff(c_702, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_695])).
% 46.60/35.60  tff(c_38, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_119])).
% 46.60/35.60  tff(c_30, plain, (![A_23]: (m1_subset_1(k6_relat_1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 46.60/35.60  tff(c_77, plain, (![A_23]: (m1_subset_1(k6_partfun1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30])).
% 46.60/35.60  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 46.60/35.60  tff(c_302, plain, (![D_83, C_84, A_85, B_86]: (D_83=C_84 | ~r2_relset_1(A_85, B_86, C_84, D_83) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 46.60/35.60  tff(c_310, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_62, c_302])).
% 46.60/35.60  tff(c_325, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_310])).
% 46.60/35.60  tff(c_388, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_325])).
% 46.60/35.60  tff(c_707, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_702, c_388])).
% 46.60/35.60  tff(c_723, plain, (![E_143, A_145, C_141, B_142, D_146, F_144]: (m1_subset_1(k1_partfun1(A_145, B_142, C_141, D_146, E_143, F_144), k1_zfmisc_1(k2_zfmisc_1(A_145, D_146))) | ~m1_subset_1(F_144, k1_zfmisc_1(k2_zfmisc_1(C_141, D_146))) | ~v1_funct_1(F_144) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(A_145, B_142))) | ~v1_funct_1(E_143))), inference(cnfTransformation, [status(thm)], [f_107])).
% 46.60/35.60  tff(c_759, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_702, c_723])).
% 46.60/35.60  tff(c_781, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_759])).
% 46.60/35.60  tff(c_783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_707, c_781])).
% 46.60/35.60  tff(c_784, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_325])).
% 46.60/35.60  tff(c_1204, plain, (![E_199, C_197, D_202, B_198, A_201, F_200]: (v1_funct_1(k1_partfun1(A_201, B_198, C_197, D_202, E_199, F_200)) | ~m1_subset_1(F_200, k1_zfmisc_1(k2_zfmisc_1(C_197, D_202))) | ~v1_funct_1(F_200) | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(A_201, B_198))) | ~v1_funct_1(E_199))), inference(cnfTransformation, [status(thm)], [f_107])).
% 46.60/35.60  tff(c_1210, plain, (![A_201, B_198, E_199]: (v1_funct_1(k1_partfun1(A_201, B_198, '#skF_2', '#skF_1', E_199, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(A_201, B_198))) | ~v1_funct_1(E_199))), inference(resolution, [status(thm)], [c_66, c_1204])).
% 46.60/35.60  tff(c_1236, plain, (![A_207, B_208, E_209]: (v1_funct_1(k1_partfun1(A_207, B_208, '#skF_2', '#skF_1', E_209, '#skF_4')) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~v1_funct_1(E_209))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1210])).
% 46.60/35.60  tff(c_1242, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1236])).
% 46.60/35.60  tff(c_1249, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_784, c_1242])).
% 46.60/35.60  tff(c_8, plain, (![A_5]: (k2_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 46.60/35.60  tff(c_81, plain, (![A_5]: (k2_relat_1(k6_partfun1(A_5))=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8])).
% 46.60/35.60  tff(c_14, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 46.60/35.60  tff(c_80, plain, (![A_7]: (v1_relat_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_14])).
% 46.60/35.60  tff(c_142, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 46.60/35.60  tff(c_154, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_142])).
% 46.60/35.60  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_204])).
% 46.60/35.60  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_204])).
% 46.60/35.60  tff(c_196, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 46.60/35.60  tff(c_202, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_196])).
% 46.60/35.60  tff(c_209, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_202])).
% 46.60/35.60  tff(c_20, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_relat_1(k2_relat_1(A_10))!=k5_relat_1(B_12, A_10) | k2_relat_1(B_12)!=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_77])).
% 46.60/35.60  tff(c_1151, plain, (![A_194, B_195]: (k2_funct_1(A_194)=B_195 | k6_partfun1(k2_relat_1(A_194))!=k5_relat_1(B_195, A_194) | k2_relat_1(B_195)!=k1_relat_1(A_194) | ~v2_funct_1(A_194) | ~v1_funct_1(B_195) | ~v1_relat_1(B_195) | ~v1_funct_1(A_194) | ~v1_relat_1(A_194))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_20])).
% 46.60/35.60  tff(c_1161, plain, (![B_195]: (k2_funct_1('#skF_3')=B_195 | k5_relat_1(B_195, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_195)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_195) | ~v1_relat_1(B_195) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_209, c_1151])).
% 46.60/35.60  tff(c_1170, plain, (![B_196]: (k2_funct_1('#skF_3')=B_196 | k5_relat_1(B_196, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_196)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_196) | ~v1_relat_1(B_196))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_76, c_60, c_1161])).
% 46.60/35.60  tff(c_1188, plain, (![A_7]: (k6_partfun1(A_7)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_7), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_7))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_7)))), inference(resolution, [status(thm)], [c_80, c_1170])).
% 46.60/35.60  tff(c_1269, plain, (![A_217]: (k6_partfun1(A_217)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_217), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_217 | ~v1_funct_1(k6_partfun1(A_217)))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1188])).
% 46.60/35.60  tff(c_1273, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_1249, c_1269])).
% 46.60/35.60  tff(c_1274, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1273])).
% 46.60/35.60  tff(c_12, plain, (![A_6]: (v1_relat_1(k2_funct_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 46.60/35.60  tff(c_4, plain, (![A_4]: (k10_relat_1(A_4, k2_relat_1(A_4))=k1_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 46.60/35.60  tff(c_217, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_209, c_4])).
% 46.60/35.60  tff(c_223, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_217])).
% 46.60/35.60  tff(c_18, plain, (![B_9, A_8]: (k9_relat_1(k2_funct_1(B_9), A_8)=k10_relat_1(B_9, A_8) | ~v2_funct_1(B_9) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 46.60/35.60  tff(c_2, plain, (![B_3, A_1]: (k9_relat_1(B_3, k2_relat_1(A_1))=k2_relat_1(k5_relat_1(A_1, B_3)) | ~v1_relat_1(B_3) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 46.60/35.60  tff(c_214, plain, (![B_3]: (k2_relat_1(k5_relat_1('#skF_3', B_3))=k9_relat_1(B_3, '#skF_2') | ~v1_relat_1(B_3) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_209, c_2])).
% 46.60/35.60  tff(c_259, plain, (![B_79]: (k2_relat_1(k5_relat_1('#skF_3', B_79))=k9_relat_1(B_79, '#skF_2') | ~v1_relat_1(B_79))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_214])).
% 46.60/35.60  tff(c_274, plain, (![B_80]: (k10_relat_1(k5_relat_1('#skF_3', B_80), k9_relat_1(B_80, '#skF_2'))=k1_relat_1(k5_relat_1('#skF_3', B_80)) | ~v1_relat_1(k5_relat_1('#skF_3', B_80)) | ~v1_relat_1(B_80))), inference(superposition, [status(thm), theory('equality')], [c_259, c_4])).
% 46.60/35.60  tff(c_816, plain, (![B_150]: (k10_relat_1(k5_relat_1('#skF_3', k2_funct_1(B_150)), k10_relat_1(B_150, '#skF_2'))=k1_relat_1(k5_relat_1('#skF_3', k2_funct_1(B_150))) | ~v1_relat_1(k5_relat_1('#skF_3', k2_funct_1(B_150))) | ~v1_relat_1(k2_funct_1(B_150)) | ~v2_funct_1(B_150) | ~v1_funct_1(B_150) | ~v1_relat_1(B_150))), inference(superposition, [status(thm), theory('equality')], [c_18, c_274])).
% 46.60/35.60  tff(c_825, plain, (k10_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k1_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3'))) | ~v1_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_223, c_816])).
% 46.60/35.60  tff(c_833, plain, (k10_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k1_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3'))) | ~v1_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_76, c_60, c_825])).
% 46.60/35.60  tff(c_836, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_833])).
% 46.60/35.60  tff(c_839, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_836])).
% 46.60/35.60  tff(c_843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_76, c_839])).
% 46.60/35.60  tff(c_845, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_833])).
% 46.60/35.60  tff(c_56, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_204])).
% 46.60/35.60  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_204])).
% 46.60/35.60  tff(c_1400, plain, (![A_228, C_229, B_230]: (k6_partfun1(A_228)=k5_relat_1(C_229, k2_funct_1(C_229)) | k1_xboole_0=B_230 | ~v2_funct_1(C_229) | k2_relset_1(A_228, B_230, C_229)!=B_230 | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_228, B_230))) | ~v1_funct_2(C_229, A_228, B_230) | ~v1_funct_1(C_229))), inference(cnfTransformation, [status(thm)], [f_178])).
% 46.60/35.60  tff(c_1404, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1400])).
% 46.60/35.60  tff(c_1412, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_64, c_60, c_1404])).
% 46.60/35.60  tff(c_1413, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_1412])).
% 46.60/35.60  tff(c_238, plain, (![B_77, A_78]: (k9_relat_1(k2_funct_1(B_77), A_78)=k10_relat_1(B_77, A_78) | ~v2_funct_1(B_77) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_60])).
% 46.60/35.60  tff(c_245, plain, (![A_1, B_77]: (k2_relat_1(k5_relat_1(A_1, k2_funct_1(B_77)))=k10_relat_1(B_77, k2_relat_1(A_1)) | ~v1_relat_1(k2_funct_1(B_77)) | ~v1_relat_1(A_1) | ~v2_funct_1(B_77) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(superposition, [status(thm), theory('equality')], [c_238, c_2])).
% 46.60/35.60  tff(c_1431, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_relat_1(k6_partfun1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1413, c_245])).
% 46.60/35.60  tff(c_1448, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_76, c_60, c_154, c_845, c_81, c_223, c_209, c_1431])).
% 46.60/35.60  tff(c_1450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1274, c_1448])).
% 46.60/35.60  tff(c_1452, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1273])).
% 46.60/35.60  tff(c_54, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_204])).
% 46.60/35.60  tff(c_155, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_142])).
% 46.60/35.60  tff(c_1179, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_155, c_1170])).
% 46.60/35.60  tff(c_1194, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1179])).
% 46.60/35.60  tff(c_1195, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_1194])).
% 46.60/35.60  tff(c_1202, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1195])).
% 46.60/35.60  tff(c_1455, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1452, c_1202])).
% 46.60/35.60  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_204])).
% 46.60/35.60  tff(c_156, plain, (![A_65, B_66, D_67]: (r2_relset_1(A_65, B_66, D_67, D_67) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 46.60/35.60  tff(c_163, plain, (![A_23]: (r2_relset_1(A_23, A_23, k6_partfun1(A_23), k6_partfun1(A_23)))), inference(resolution, [status(thm)], [c_77, c_156])).
% 46.60/35.60  tff(c_210, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_196])).
% 46.60/35.60  tff(c_2023, plain, (![A_258, B_259, C_260, D_261]: (k2_relset_1(A_258, B_259, C_260)=B_259 | ~r2_relset_1(B_259, B_259, k1_partfun1(B_259, A_258, A_258, B_259, D_261, C_260), k6_partfun1(B_259)) | ~m1_subset_1(D_261, k1_zfmisc_1(k2_zfmisc_1(B_259, A_258))) | ~v1_funct_2(D_261, B_259, A_258) | ~v1_funct_1(D_261) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))) | ~v1_funct_2(C_260, A_258, B_259) | ~v1_funct_1(C_260))), inference(cnfTransformation, [status(thm)], [f_136])).
% 46.60/35.60  tff(c_2029, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_784, c_2023])).
% 46.60/35.60  tff(c_2033, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_163, c_210, c_2029])).
% 46.60/35.60  tff(c_2035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1455, c_2033])).
% 46.60/35.60  tff(c_2036, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1195])).
% 46.60/35.60  tff(c_2454, plain, (![B_301, A_303, D_305, C_300, F_302, E_304]: (k1_partfun1(A_303, B_301, C_300, D_305, E_304, F_302)=k5_relat_1(E_304, F_302) | ~m1_subset_1(F_302, k1_zfmisc_1(k2_zfmisc_1(C_300, D_305))) | ~v1_funct_1(F_302) | ~m1_subset_1(E_304, k1_zfmisc_1(k2_zfmisc_1(A_303, B_301))) | ~v1_funct_1(E_304))), inference(cnfTransformation, [status(thm)], [f_117])).
% 46.60/35.60  tff(c_2460, plain, (![A_303, B_301, E_304]: (k1_partfun1(A_303, B_301, '#skF_2', '#skF_1', E_304, '#skF_4')=k5_relat_1(E_304, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_304, k1_zfmisc_1(k2_zfmisc_1(A_303, B_301))) | ~v1_funct_1(E_304))), inference(resolution, [status(thm)], [c_66, c_2454])).
% 46.60/35.60  tff(c_3161, plain, (![A_345, B_346, E_347]: (k1_partfun1(A_345, B_346, '#skF_2', '#skF_1', E_347, '#skF_4')=k5_relat_1(E_347, '#skF_4') | ~m1_subset_1(E_347, k1_zfmisc_1(k2_zfmisc_1(A_345, B_346))) | ~v1_funct_1(E_347))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2460])).
% 46.60/35.60  tff(c_3167, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_3161])).
% 46.60/35.60  tff(c_3174, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_784, c_3167])).
% 46.60/35.60  tff(c_58, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_204])).
% 46.60/35.60  tff(c_2115, plain, (![E_267, A_269, B_266, F_268, D_270, C_265]: (v1_funct_1(k1_partfun1(A_269, B_266, C_265, D_270, E_267, F_268)) | ~m1_subset_1(F_268, k1_zfmisc_1(k2_zfmisc_1(C_265, D_270))) | ~v1_funct_1(F_268) | ~m1_subset_1(E_267, k1_zfmisc_1(k2_zfmisc_1(A_269, B_266))) | ~v1_funct_1(E_267))), inference(cnfTransformation, [status(thm)], [f_107])).
% 46.60/35.60  tff(c_2121, plain, (![A_269, B_266, E_267]: (v1_funct_1(k1_partfun1(A_269, B_266, '#skF_2', '#skF_1', E_267, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_267, k1_zfmisc_1(k2_zfmisc_1(A_269, B_266))) | ~v1_funct_1(E_267))), inference(resolution, [status(thm)], [c_66, c_2115])).
% 46.60/35.60  tff(c_2146, plain, (![A_274, B_275, E_276]: (v1_funct_1(k1_partfun1(A_274, B_275, '#skF_2', '#skF_1', E_276, '#skF_4')) | ~m1_subset_1(E_276, k1_zfmisc_1(k2_zfmisc_1(A_274, B_275))) | ~v1_funct_1(E_276))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2121])).
% 46.60/35.60  tff(c_2152, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_2146])).
% 46.60/35.60  tff(c_2159, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_784, c_2152])).
% 46.60/35.60  tff(c_1201, plain, (![A_7]: (k6_partfun1(A_7)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_7), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_7 | ~v1_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1188])).
% 46.60/35.60  tff(c_2166, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_2159, c_1201])).
% 46.60/35.60  tff(c_2169, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2166])).
% 46.60/35.60  tff(c_2322, plain, (![A_296, C_297, B_298]: (k6_partfun1(A_296)=k5_relat_1(C_297, k2_funct_1(C_297)) | k1_xboole_0=B_298 | ~v2_funct_1(C_297) | k2_relset_1(A_296, B_298, C_297)!=B_298 | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_296, B_298))) | ~v1_funct_2(C_297, A_296, B_298) | ~v1_funct_1(C_297))), inference(cnfTransformation, [status(thm)], [f_178])).
% 46.60/35.60  tff(c_2326, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_2322])).
% 46.60/35.60  tff(c_2334, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_64, c_60, c_2326])).
% 46.60/35.60  tff(c_2335, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_2334])).
% 46.60/35.60  tff(c_2353, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k2_relat_1(k6_partfun1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2335, c_245])).
% 46.60/35.60  tff(c_2370, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_76, c_60, c_154, c_845, c_81, c_223, c_209, c_2353])).
% 46.60/35.60  tff(c_2372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2169, c_2370])).
% 46.60/35.60  tff(c_2374, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2166])).
% 46.60/35.60  tff(c_2037, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1195])).
% 46.60/35.60  tff(c_2038, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2037, c_210])).
% 46.60/35.60  tff(c_2380, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2374, c_2038])).
% 46.60/35.60  tff(c_2500, plain, (![A_309, C_310, B_311]: (k6_partfun1(A_309)=k5_relat_1(C_310, k2_funct_1(C_310)) | k1_xboole_0=B_311 | ~v2_funct_1(C_310) | k2_relset_1(A_309, B_311, C_310)!=B_311 | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(A_309, B_311))) | ~v1_funct_2(C_310, A_309, B_311) | ~v1_funct_1(C_310))), inference(cnfTransformation, [status(thm)], [f_178])).
% 46.60/35.60  tff(c_2506, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_2500])).
% 46.60/35.60  tff(c_2516, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_2380, c_2506])).
% 46.60/35.60  tff(c_2517, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_2516])).
% 46.60/35.60  tff(c_2585, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2517])).
% 46.60/35.60  tff(c_16, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 46.60/35.60  tff(c_79, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_16])).
% 46.60/35.60  tff(c_3035, plain, (![C_338, A_336, E_337, D_334, B_335]: (k1_xboole_0=C_338 | v2_funct_1(E_337) | k2_relset_1(A_336, B_335, D_334)!=B_335 | ~v2_funct_1(k1_partfun1(A_336, B_335, B_335, C_338, D_334, E_337)) | ~m1_subset_1(E_337, k1_zfmisc_1(k2_zfmisc_1(B_335, C_338))) | ~v1_funct_2(E_337, B_335, C_338) | ~v1_funct_1(E_337) | ~m1_subset_1(D_334, k1_zfmisc_1(k2_zfmisc_1(A_336, B_335))) | ~v1_funct_2(D_334, A_336, B_335) | ~v1_funct_1(D_334))), inference(cnfTransformation, [status(thm)], [f_162])).
% 46.60/35.60  tff(c_3041, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_784, c_3035])).
% 46.60/35.60  tff(c_3049, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_66, c_79, c_64, c_3041])).
% 46.60/35.60  tff(c_3051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2585, c_58, c_3049])).
% 46.60/35.60  tff(c_3053, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2517])).
% 46.60/35.60  tff(c_2047, plain, (k10_relat_1('#skF_4', k1_relat_1('#skF_3'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2037, c_4])).
% 46.60/35.60  tff(c_2055, plain, (k10_relat_1('#skF_4', k1_relat_1('#skF_3'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_2047])).
% 46.60/35.60  tff(c_2378, plain, (k10_relat_1('#skF_4', '#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2374, c_2055])).
% 46.60/35.60  tff(c_2381, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2374, c_2037])).
% 46.60/35.60  tff(c_3052, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2517])).
% 46.60/35.60  tff(c_3060, plain, (k10_relat_1('#skF_4', k2_relat_1('#skF_4'))=k2_relat_1(k6_partfun1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3052, c_245])).
% 46.60/35.60  tff(c_3065, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_70, c_3053, c_155, c_81, c_2378, c_2381, c_3060])).
% 46.60/35.60  tff(c_3067, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3065])).
% 46.60/35.60  tff(c_3087, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_3067])).
% 46.60/35.60  tff(c_3091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_70, c_3087])).
% 46.60/35.60  tff(c_3092, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_3065])).
% 46.60/35.60  tff(c_78, plain, (![A_10, B_12]: (k2_funct_1(A_10)=B_12 | k6_partfun1(k2_relat_1(A_10))!=k5_relat_1(B_12, A_10) | k2_relat_1(B_12)!=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_20])).
% 46.60/35.60  tff(c_2041, plain, (![B_12]: (k2_funct_1('#skF_4')=B_12 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_12, '#skF_4') | k2_relat_1(B_12)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2037, c_78])).
% 46.60/35.60  tff(c_2051, plain, (![B_12]: (k2_funct_1('#skF_4')=B_12 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_12, '#skF_4') | k2_relat_1(B_12)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_70, c_2041])).
% 46.60/35.60  tff(c_49492, plain, (![B_1215]: (k2_funct_1('#skF_4')=B_1215 | k5_relat_1(B_1215, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_1215)!='#skF_2' | ~v1_funct_1(B_1215) | ~v1_relat_1(B_1215))), inference(demodulation, [status(thm), theory('equality')], [c_3053, c_3092, c_2374, c_2051])).
% 46.60/35.60  tff(c_50386, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_154, c_49492])).
% 46.60/35.60  tff(c_51139, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_209, c_3174, c_50386])).
% 46.60/35.60  tff(c_51149, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_51139, c_3052])).
% 46.60/35.60  tff(c_51154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2036, c_51149])).
% 46.60/35.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 46.60/35.60  
% 46.60/35.60  Inference rules
% 46.60/35.60  ----------------------
% 46.60/35.60  #Ref     : 0
% 46.60/35.60  #Sup     : 10400
% 46.60/35.60  #Fact    : 0
% 46.60/35.60  #Define  : 0
% 46.60/35.60  #Split   : 91
% 46.60/35.60  #Chain   : 0
% 46.60/35.60  #Close   : 0
% 46.60/35.60  
% 46.60/35.60  Ordering : KBO
% 46.60/35.60  
% 46.60/35.60  Simplification rules
% 46.60/35.60  ----------------------
% 46.60/35.60  #Subsume      : 821
% 46.60/35.60  #Demod        : 40944
% 46.60/35.60  #Tautology    : 1002
% 46.60/35.60  #SimpNegUnit  : 1156
% 46.60/35.60  #BackRed      : 108
% 46.60/35.60  
% 46.60/35.60  #Partial instantiations: 0
% 46.60/35.60  #Strategies tried      : 1
% 46.60/35.60  
% 46.60/35.60  Timing (in seconds)
% 46.60/35.60  ----------------------
% 46.60/35.60  Preprocessing        : 0.40
% 46.60/35.60  Parsing              : 0.21
% 46.60/35.60  CNF conversion       : 0.03
% 46.60/35.60  Main loop            : 34.40
% 46.60/35.60  Inferencing          : 4.35
% 46.60/35.60  Reduction            : 22.24
% 46.60/35.60  Demodulation         : 20.48
% 46.60/35.60  BG Simplification    : 0.28
% 46.60/35.60  Subsumption          : 6.58
% 46.60/35.60  Abstraction          : 0.63
% 46.60/35.60  MUC search           : 0.00
% 46.60/35.60  Cooper               : 0.00
% 46.60/35.60  Total                : 34.86
% 46.60/35.60  Index Insertion      : 0.00
% 46.60/35.60  Index Deletion       : 0.00
% 46.60/35.60  Index Matching       : 0.00
% 46.60/35.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
