%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:09 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 344 expanded)
%              Number of leaves         :   41 ( 137 expanded)
%              Depth                    :   11
%              Number of atoms          :  218 ( 965 expanded)
%              Number of equality atoms :   42 ( 105 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_95,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_42,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_73,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_134,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_112,axiom,(
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

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_197,plain,(
    ! [C_70,B_71,A_72] :
      ( v1_xboole_0(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(B_71,A_72)))
      | ~ v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_214,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_197])).

tff(c_218,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_46,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_97,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_58,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_52,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_38,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_12,plain,(
    ! [A_5] : v2_funct_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_62,plain,(
    ! [A_5] : v2_funct_1(k6_partfun1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12])).

tff(c_34,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] :
      ( m1_subset_1(k1_partfun1(A_26,B_27,C_28,D_29,E_30,F_31),k1_zfmisc_1(k2_zfmisc_1(A_26,D_29)))
      | ~ m1_subset_1(F_31,k1_zfmisc_1(k2_zfmisc_1(C_28,D_29)))
      | ~ v1_funct_1(F_31)
      | ~ m1_subset_1(E_30,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_1(E_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    ! [A_23] : m1_subset_1(k6_relat_1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_61,plain,(
    ! [A_23] : m1_subset_1(k6_partfun1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28])).

tff(c_48,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_409,plain,(
    ! [D_89,C_90,A_91,B_92] :
      ( D_89 = C_90
      | ~ r2_relset_1(A_91,B_92,C_90,D_89)
      | ~ m1_subset_1(D_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_415,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_48,c_409])).

tff(c_426,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_415])).

tff(c_667,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_426])).

tff(c_986,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_667])).

tff(c_990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_50,c_986])).

tff(c_991,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_426])).

tff(c_1032,plain,(
    ! [B_155,D_157,A_154,C_156,E_158] :
      ( k1_xboole_0 = C_156
      | v2_funct_1(D_157)
      | ~ v2_funct_1(k1_partfun1(A_154,B_155,B_155,C_156,D_157,E_158))
      | ~ m1_subset_1(E_158,k1_zfmisc_1(k2_zfmisc_1(B_155,C_156)))
      | ~ v1_funct_2(E_158,B_155,C_156)
      | ~ v1_funct_1(E_158)
      | ~ m1_subset_1(D_157,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155)))
      | ~ v1_funct_2(D_157,A_154,B_155)
      | ~ v1_funct_1(D_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1034,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_991,c_1032])).

tff(c_1036,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_50,c_62,c_1034])).

tff(c_1037,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_1036])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1067,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1037,c_2])).

tff(c_1069,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_1067])).

tff(c_1070,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_1178,plain,(
    ! [A_164] :
      ( v1_xboole_0(k6_partfun1(A_164))
      | ~ v1_xboole_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_61,c_197])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1078,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_1070,c_4])).

tff(c_1194,plain,(
    ! [A_168] :
      ( k6_partfun1(A_168) = '#skF_4'
      | ~ v1_xboole_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_1178,c_1078])).

tff(c_1202,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1070,c_1194])).

tff(c_1221,plain,(
    v2_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1202,c_62])).

tff(c_98,plain,(
    ! [B_49,A_50] :
      ( ~ v1_xboole_0(B_49)
      | B_49 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_101,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_2,c_98])).

tff(c_1077,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1070,c_101])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1092,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_1077,c_10])).

tff(c_1071,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_1084,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1071,c_101])).

tff(c_1100,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_1084])).

tff(c_1106,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1100,c_56])).

tff(c_1264,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1092,c_1106])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_212,plain,(
    ! [C_70] :
      ( v1_xboole_0(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_197])).

tff(c_217,plain,(
    ! [C_70] :
      ( v1_xboole_0(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_212])).

tff(c_1257,plain,(
    ! [C_70] :
      ( v1_xboole_0(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_217])).

tff(c_1268,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1264,c_1257])).

tff(c_1278,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1268,c_1078])).

tff(c_1286,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1278,c_97])).

tff(c_1294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1221,c_1286])).

tff(c_1295,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1317,plain,(
    ! [C_177,A_178,B_179] :
      ( v1_relat_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1332,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1317])).

tff(c_1352,plain,(
    ! [C_184,B_185,A_186] :
      ( v5_relat_1(C_184,B_185)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_186,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1369,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1352])).

tff(c_1470,plain,(
    ! [A_201,B_202,D_203] :
      ( r2_relset_1(A_201,B_202,D_203,D_203)
      | ~ m1_subset_1(D_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1481,plain,(
    ! [A_23] : r2_relset_1(A_23,A_23,k6_partfun1(A_23),k6_partfun1(A_23)) ),
    inference(resolution,[status(thm)],[c_61,c_1470])).

tff(c_1578,plain,(
    ! [A_209,B_210,C_211] :
      ( k2_relset_1(A_209,B_210,C_211) = k2_relat_1(C_211)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1595,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1578])).

tff(c_1611,plain,(
    ! [D_213,C_214,A_215,B_216] :
      ( D_213 = C_214
      | ~ r2_relset_1(A_215,B_216,C_214,D_213)
      | ~ m1_subset_1(D_213,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216)))
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1617,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_48,c_1611])).

tff(c_1628,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_1617])).

tff(c_1860,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1628])).

tff(c_2219,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1860])).

tff(c_2223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_50,c_2219])).

tff(c_2224,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1628])).

tff(c_2677,plain,(
    ! [A_295,B_296,C_297,D_298] :
      ( k2_relset_1(A_295,B_296,C_297) = B_296
      | ~ r2_relset_1(B_296,B_296,k1_partfun1(B_296,A_295,A_295,B_296,D_298,C_297),k6_partfun1(B_296))
      | ~ m1_subset_1(D_298,k1_zfmisc_1(k2_zfmisc_1(B_296,A_295)))
      | ~ v1_funct_2(D_298,B_296,A_295)
      | ~ v1_funct_1(D_298)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_295,B_296)))
      | ~ v1_funct_2(C_297,A_295,B_296)
      | ~ v1_funct_1(C_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2686,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2224,c_2677])).

tff(c_2694,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_60,c_58,c_56,c_1481,c_1595,c_2686])).

tff(c_30,plain,(
    ! [B_25] :
      ( v2_funct_2(B_25,k2_relat_1(B_25))
      | ~ v5_relat_1(B_25,k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2700,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2694,c_30])).

tff(c_2704,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1332,c_1369,c_2694,c_2700])).

tff(c_2706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1295,c_2704])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.81  
% 4.69/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.82  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.69/1.82  
% 4.69/1.82  %Foreground sorts:
% 4.69/1.82  
% 4.69/1.82  
% 4.69/1.82  %Background operators:
% 4.69/1.82  
% 4.69/1.82  
% 4.69/1.82  %Foreground operators:
% 4.69/1.82  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.69/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.69/1.82  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.69/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/1.82  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.69/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.69/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.69/1.82  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.69/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.69/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.69/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.69/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.69/1.82  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.69/1.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.69/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.69/1.82  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.69/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.69/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.69/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.69/1.82  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.69/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/1.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.69/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.69/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.69/1.82  
% 4.76/1.83  tff(f_154, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 4.76/1.83  tff(f_59, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.76/1.83  tff(f_95, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.76/1.83  tff(f_42, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 4.76/1.83  tff(f_93, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.76/1.83  tff(f_73, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.76/1.83  tff(f_71, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.76/1.83  tff(f_134, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 4.76/1.83  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.76/1.83  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.76/1.83  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.76/1.83  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.76/1.83  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.76/1.83  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.76/1.83  tff(f_112, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.76/1.83  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.76/1.83  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.76/1.83  tff(c_197, plain, (![C_70, B_71, A_72]: (v1_xboole_0(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(B_71, A_72))) | ~v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.76/1.83  tff(c_214, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_197])).
% 4.76/1.83  tff(c_218, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_214])).
% 4.76/1.83  tff(c_46, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.76/1.83  tff(c_97, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 4.76/1.83  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.76/1.83  tff(c_58, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.76/1.83  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.76/1.83  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.76/1.83  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.76/1.83  tff(c_38, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.76/1.83  tff(c_12, plain, (![A_5]: (v2_funct_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.76/1.83  tff(c_62, plain, (![A_5]: (v2_funct_1(k6_partfun1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12])).
% 4.76/1.83  tff(c_34, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (m1_subset_1(k1_partfun1(A_26, B_27, C_28, D_29, E_30, F_31), k1_zfmisc_1(k2_zfmisc_1(A_26, D_29))) | ~m1_subset_1(F_31, k1_zfmisc_1(k2_zfmisc_1(C_28, D_29))) | ~v1_funct_1(F_31) | ~m1_subset_1(E_30, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_1(E_30))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.76/1.83  tff(c_28, plain, (![A_23]: (m1_subset_1(k6_relat_1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.76/1.83  tff(c_61, plain, (![A_23]: (m1_subset_1(k6_partfun1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28])).
% 4.76/1.83  tff(c_48, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.76/1.83  tff(c_409, plain, (![D_89, C_90, A_91, B_92]: (D_89=C_90 | ~r2_relset_1(A_91, B_92, C_90, D_89) | ~m1_subset_1(D_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.76/1.83  tff(c_415, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_48, c_409])).
% 4.76/1.83  tff(c_426, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_415])).
% 4.76/1.83  tff(c_667, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_426])).
% 4.76/1.83  tff(c_986, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_667])).
% 4.76/1.83  tff(c_990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_50, c_986])).
% 4.76/1.83  tff(c_991, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_426])).
% 4.76/1.83  tff(c_1032, plain, (![B_155, D_157, A_154, C_156, E_158]: (k1_xboole_0=C_156 | v2_funct_1(D_157) | ~v2_funct_1(k1_partfun1(A_154, B_155, B_155, C_156, D_157, E_158)) | ~m1_subset_1(E_158, k1_zfmisc_1(k2_zfmisc_1(B_155, C_156))) | ~v1_funct_2(E_158, B_155, C_156) | ~v1_funct_1(E_158) | ~m1_subset_1(D_157, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))) | ~v1_funct_2(D_157, A_154, B_155) | ~v1_funct_1(D_157))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.76/1.83  tff(c_1034, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_991, c_1032])).
% 4.76/1.83  tff(c_1036, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_50, c_62, c_1034])).
% 4.76/1.83  tff(c_1037, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_97, c_1036])).
% 4.76/1.83  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.76/1.83  tff(c_1067, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1037, c_2])).
% 4.76/1.83  tff(c_1069, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_1067])).
% 4.76/1.83  tff(c_1070, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_214])).
% 4.76/1.83  tff(c_1178, plain, (![A_164]: (v1_xboole_0(k6_partfun1(A_164)) | ~v1_xboole_0(A_164))), inference(resolution, [status(thm)], [c_61, c_197])).
% 4.76/1.83  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.76/1.83  tff(c_1078, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_1070, c_4])).
% 4.76/1.83  tff(c_1194, plain, (![A_168]: (k6_partfun1(A_168)='#skF_4' | ~v1_xboole_0(A_168))), inference(resolution, [status(thm)], [c_1178, c_1078])).
% 4.76/1.83  tff(c_1202, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_1070, c_1194])).
% 4.76/1.83  tff(c_1221, plain, (v2_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1202, c_62])).
% 4.76/1.83  tff(c_98, plain, (![B_49, A_50]: (~v1_xboole_0(B_49) | B_49=A_50 | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.76/1.83  tff(c_101, plain, (![A_50]: (k1_xboole_0=A_50 | ~v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_2, c_98])).
% 4.76/1.83  tff(c_1077, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1070, c_101])).
% 4.76/1.83  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.76/1.83  tff(c_1092, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_1077, c_10])).
% 4.76/1.83  tff(c_1071, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_214])).
% 4.76/1.83  tff(c_1084, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1071, c_101])).
% 4.76/1.83  tff(c_1100, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_1084])).
% 4.76/1.83  tff(c_1106, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1100, c_56])).
% 4.76/1.83  tff(c_1264, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1092, c_1106])).
% 4.76/1.83  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.76/1.83  tff(c_212, plain, (![C_70]: (v1_xboole_0(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_197])).
% 4.76/1.83  tff(c_217, plain, (![C_70]: (v1_xboole_0(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_212])).
% 4.76/1.83  tff(c_1257, plain, (![C_70]: (v1_xboole_0(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_217])).
% 4.76/1.83  tff(c_1268, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1264, c_1257])).
% 4.76/1.83  tff(c_1278, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1268, c_1078])).
% 4.76/1.83  tff(c_1286, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1278, c_97])).
% 4.76/1.83  tff(c_1294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1221, c_1286])).
% 4.76/1.83  tff(c_1295, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 4.76/1.83  tff(c_1317, plain, (![C_177, A_178, B_179]: (v1_relat_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.76/1.83  tff(c_1332, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1317])).
% 4.76/1.83  tff(c_1352, plain, (![C_184, B_185, A_186]: (v5_relat_1(C_184, B_185) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_186, B_185))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.76/1.83  tff(c_1369, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_1352])).
% 4.76/1.83  tff(c_1470, plain, (![A_201, B_202, D_203]: (r2_relset_1(A_201, B_202, D_203, D_203) | ~m1_subset_1(D_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.76/1.83  tff(c_1481, plain, (![A_23]: (r2_relset_1(A_23, A_23, k6_partfun1(A_23), k6_partfun1(A_23)))), inference(resolution, [status(thm)], [c_61, c_1470])).
% 4.76/1.83  tff(c_1578, plain, (![A_209, B_210, C_211]: (k2_relset_1(A_209, B_210, C_211)=k2_relat_1(C_211) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.76/1.83  tff(c_1595, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1578])).
% 4.76/1.83  tff(c_1611, plain, (![D_213, C_214, A_215, B_216]: (D_213=C_214 | ~r2_relset_1(A_215, B_216, C_214, D_213) | ~m1_subset_1(D_213, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.76/1.83  tff(c_1617, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_48, c_1611])).
% 4.76/1.83  tff(c_1628, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_1617])).
% 4.76/1.83  tff(c_1860, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1628])).
% 4.76/1.83  tff(c_2219, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_1860])).
% 4.76/1.83  tff(c_2223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_50, c_2219])).
% 4.76/1.83  tff(c_2224, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1628])).
% 4.76/1.83  tff(c_2677, plain, (![A_295, B_296, C_297, D_298]: (k2_relset_1(A_295, B_296, C_297)=B_296 | ~r2_relset_1(B_296, B_296, k1_partfun1(B_296, A_295, A_295, B_296, D_298, C_297), k6_partfun1(B_296)) | ~m1_subset_1(D_298, k1_zfmisc_1(k2_zfmisc_1(B_296, A_295))) | ~v1_funct_2(D_298, B_296, A_295) | ~v1_funct_1(D_298) | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_295, B_296))) | ~v1_funct_2(C_297, A_295, B_296) | ~v1_funct_1(C_297))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.76/1.83  tff(c_2686, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2224, c_2677])).
% 4.76/1.83  tff(c_2694, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_60, c_58, c_56, c_1481, c_1595, c_2686])).
% 4.76/1.83  tff(c_30, plain, (![B_25]: (v2_funct_2(B_25, k2_relat_1(B_25)) | ~v5_relat_1(B_25, k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.76/1.83  tff(c_2700, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2694, c_30])).
% 4.76/1.83  tff(c_2704, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1332, c_1369, c_2694, c_2700])).
% 4.76/1.83  tff(c_2706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1295, c_2704])).
% 4.76/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.76/1.83  
% 4.76/1.83  Inference rules
% 4.76/1.83  ----------------------
% 4.76/1.83  #Ref     : 0
% 4.76/1.83  #Sup     : 655
% 4.76/1.83  #Fact    : 0
% 4.76/1.83  #Define  : 0
% 4.76/1.83  #Split   : 12
% 4.76/1.83  #Chain   : 0
% 4.76/1.83  #Close   : 0
% 4.76/1.83  
% 4.76/1.83  Ordering : KBO
% 4.76/1.83  
% 4.76/1.83  Simplification rules
% 4.76/1.83  ----------------------
% 4.76/1.83  #Subsume      : 77
% 4.76/1.83  #Demod        : 454
% 4.76/1.83  #Tautology    : 244
% 4.76/1.83  #SimpNegUnit  : 3
% 4.76/1.83  #BackRed      : 65
% 4.76/1.83  
% 4.76/1.83  #Partial instantiations: 0
% 4.76/1.83  #Strategies tried      : 1
% 4.76/1.84  
% 4.76/1.84  Timing (in seconds)
% 4.76/1.84  ----------------------
% 4.76/1.84  Preprocessing        : 0.35
% 4.76/1.84  Parsing              : 0.19
% 4.76/1.84  CNF conversion       : 0.02
% 4.76/1.84  Main loop            : 0.71
% 4.76/1.84  Inferencing          : 0.24
% 4.76/1.84  Reduction            : 0.24
% 4.76/1.84  Demodulation         : 0.17
% 4.76/1.84  BG Simplification    : 0.03
% 4.76/1.84  Subsumption          : 0.14
% 4.76/1.84  Abstraction          : 0.03
% 4.76/1.84  MUC search           : 0.00
% 4.76/1.84  Cooper               : 0.00
% 4.76/1.84  Total                : 1.10
% 4.76/1.84  Index Insertion      : 0.00
% 4.76/1.84  Index Deletion       : 0.00
% 4.76/1.84  Index Matching       : 0.00
% 4.76/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
