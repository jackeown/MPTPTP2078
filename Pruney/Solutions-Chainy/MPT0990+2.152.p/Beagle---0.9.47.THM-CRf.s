%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:18 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :  146 (1326 expanded)
%              Number of leaves         :   47 ( 485 expanded)
%              Depth                    :   23
%              Number of atoms          :  329 (5196 expanded)
%              Number of equality atoms :  124 (1874 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_195,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_124,axiom,(
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

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_152,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_76,axiom,(
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

tff(f_140,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_136,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_169,axiom,(
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

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_150,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_58,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_102,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_111,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_102])).

tff(c_120,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_111])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_199,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( k8_relset_1(A_72,B_73,C_74,D_75) = k10_relat_1(C_74,D_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_208,plain,(
    ! [D_75] : k8_relset_1('#skF_2','#skF_1','#skF_4',D_75) = k10_relat_1('#skF_4',D_75) ),
    inference(resolution,[status(thm)],[c_70,c_199])).

tff(c_257,plain,(
    ! [A_86,B_87,C_88] :
      ( k8_relset_1(A_86,B_87,C_88,B_87) = k1_relset_1(A_86,B_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_263,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_4','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_257])).

tff(c_269,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k10_relat_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_263])).

tff(c_299,plain,(
    ! [B_92,A_93,C_94] :
      ( k1_xboole_0 = B_92
      | k1_relset_1(A_93,B_92,C_94) = A_93
      | ~ v1_funct_2(C_94,A_93,B_92)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_308,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_299])).

tff(c_316,plain,
    ( k1_xboole_0 = '#skF_1'
    | k10_relat_1('#skF_4','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_269,c_308])).

tff(c_317,plain,(
    k10_relat_1('#skF_4','#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_316])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_108,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_102])).

tff(c_117,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_108])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_64,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_78,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_157,plain,(
    ! [A_66,B_67,C_68] :
      ( k2_relset_1(A_66,B_67,C_68) = k2_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_163,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_157])).

tff(c_169,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_163])).

tff(c_6,plain,(
    ! [A_6] :
      ( k10_relat_1(A_6,k2_relat_1(A_6)) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_174,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_6])).

tff(c_178,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_174])).

tff(c_207,plain,(
    ! [D_75] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_75) = k10_relat_1('#skF_3',D_75) ),
    inference(resolution,[status(thm)],[c_76,c_199])).

tff(c_261,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') = k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_257])).

tff(c_267,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_207,c_261])).

tff(c_305,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_299])).

tff(c_312,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_267,c_305])).

tff(c_313,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_312])).

tff(c_54,plain,(
    ! [A_45] : k6_relat_1(A_45) = k6_partfun1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_16,plain,(
    ! [A_11,B_13] :
      ( k2_funct_1(A_11) = B_13
      | k6_relat_1(k2_relat_1(A_11)) != k5_relat_1(B_13,A_11)
      | k2_relat_1(B_13) != k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_597,plain,(
    ! [A_145,B_146] :
      ( k2_funct_1(A_145) = B_146
      | k6_partfun1(k2_relat_1(A_145)) != k5_relat_1(B_146,A_145)
      | k2_relat_1(B_146) != k1_relat_1(A_145)
      | ~ v2_funct_1(A_145)
      | ~ v1_funct_1(B_146)
      | ~ v1_relat_1(B_146)
      | ~ v1_funct_1(A_145)
      | ~ v1_relat_1(A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_16])).

tff(c_599,plain,(
    ! [B_146] :
      ( k2_funct_1('#skF_3') = B_146
      | k5_relat_1(B_146,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_146) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_146)
      | ~ v1_relat_1(B_146)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_597])).

tff(c_602,plain,(
    ! [B_147] :
      ( k2_funct_1('#skF_3') = B_147
      | k5_relat_1(B_147,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_147) != '#skF_1'
      | ~ v1_funct_1(B_147)
      | ~ v1_relat_1(B_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_80,c_64,c_313,c_599])).

tff(c_605,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_602])).

tff(c_617,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_605])).

tff(c_618,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_617])).

tff(c_624,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_618])).

tff(c_50,plain,(
    ! [A_38] : m1_subset_1(k6_partfun1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_147,plain,(
    ! [A_63,B_64,D_65] :
      ( r2_relset_1(A_63,B_64,D_65,D_65)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_154,plain,(
    ! [A_38] : r2_relset_1(A_38,A_38,k6_partfun1(A_38),k6_partfun1(A_38)) ),
    inference(resolution,[status(thm)],[c_50,c_147])).

tff(c_170,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_157])).

tff(c_530,plain,(
    ! [B_140,F_141,D_144,A_143,E_139,C_142] :
      ( m1_subset_1(k1_partfun1(A_143,B_140,C_142,D_144,E_139,F_141),k1_zfmisc_1(k2_zfmisc_1(A_143,D_144)))
      | ~ m1_subset_1(F_141,k1_zfmisc_1(k2_zfmisc_1(C_142,D_144)))
      | ~ v1_funct_1(F_141)
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(A_143,B_140)))
      | ~ v1_funct_1(E_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_66,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_393,plain,(
    ! [D_106,C_107,A_108,B_109] :
      ( D_106 = C_107
      | ~ r2_relset_1(A_108,B_109,C_107,D_106)
      | ~ m1_subset_1(D_106,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_401,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_393])).

tff(c_416,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_401])).

tff(c_417,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_416])).

tff(c_546,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_530,c_417])).

tff(c_587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_546])).

tff(c_588,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_972,plain,(
    ! [A_179,B_180,C_181,D_182] :
      ( k2_relset_1(A_179,B_180,C_181) = B_180
      | ~ r2_relset_1(B_180,B_180,k1_partfun1(B_180,A_179,A_179,B_180,D_182,C_181),k6_partfun1(B_180))
      | ~ m1_subset_1(D_182,k1_zfmisc_1(k2_zfmisc_1(B_180,A_179)))
      | ~ v1_funct_2(D_182,B_180,A_179)
      | ~ v1_funct_1(D_182)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180)))
      | ~ v1_funct_2(C_181,A_179,B_180)
      | ~ v1_funct_1(C_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_975,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_588,c_972])).

tff(c_977,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_80,c_78,c_76,c_154,c_170,c_975])).

tff(c_979,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_624,c_977])).

tff(c_981,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_618])).

tff(c_989,plain,
    ( k10_relat_1('#skF_4','#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_981,c_6])).

tff(c_995,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_317,c_989])).

tff(c_81,plain,(
    ! [A_11,B_13] :
      ( k2_funct_1(A_11) = B_13
      | k6_partfun1(k2_relat_1(A_11)) != k5_relat_1(B_13,A_11)
      | k2_relat_1(B_13) != k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_16])).

tff(c_986,plain,(
    ! [B_13] :
      ( k2_funct_1('#skF_4') = B_13
      | k5_relat_1(B_13,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_13) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_981,c_81])).

tff(c_993,plain,(
    ! [B_13] :
      ( k2_funct_1('#skF_4') = B_13
      | k5_relat_1(B_13,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_13) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_74,c_986])).

tff(c_1011,plain,(
    ! [B_13] :
      ( k2_funct_1('#skF_4') = B_13
      | k5_relat_1(B_13,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_13) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_995,c_993])).

tff(c_1012,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1011])).

tff(c_10,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_10])).

tff(c_1067,plain,(
    ! [C_199,A_197,F_201,D_200,E_202,B_198] :
      ( k1_partfun1(A_197,B_198,C_199,D_200,E_202,F_201) = k5_relat_1(E_202,F_201)
      | ~ m1_subset_1(F_201,k1_zfmisc_1(k2_zfmisc_1(C_199,D_200)))
      | ~ v1_funct_1(F_201)
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ v1_funct_1(E_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1073,plain,(
    ! [A_197,B_198,E_202] :
      ( k1_partfun1(A_197,B_198,'#skF_2','#skF_1',E_202,'#skF_4') = k5_relat_1(E_202,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ v1_funct_1(E_202) ) ),
    inference(resolution,[status(thm)],[c_70,c_1067])).

tff(c_1439,plain,(
    ! [A_218,B_219,E_220] :
      ( k1_partfun1(A_218,B_219,'#skF_2','#skF_1',E_220,'#skF_4') = k5_relat_1(E_220,'#skF_4')
      | ~ m1_subset_1(E_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219)))
      | ~ v1_funct_1(E_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1073])).

tff(c_1457,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1439])).

tff(c_1474,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_588,c_1457])).

tff(c_12,plain,(
    ! [A_8,B_10] :
      ( v2_funct_1(A_8)
      | k2_relat_1(B_10) != k1_relat_1(A_8)
      | ~ v2_funct_1(k5_relat_1(B_10,A_8))
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1481,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1474,c_12])).

tff(c_1488,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_74,c_117,c_80,c_82,c_995,c_169,c_1481])).

tff(c_1490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1012,c_1488])).

tff(c_1492,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1011])).

tff(c_1493,plain,(
    ! [B_221] :
      ( k2_funct_1('#skF_4') = B_221
      | k5_relat_1(B_221,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_221) != '#skF_2'
      | ~ v1_funct_1(B_221)
      | ~ v1_relat_1(B_221) ) ),
    inference(splitRight,[status(thm)],[c_1011])).

tff(c_1499,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_1493])).

tff(c_1511,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_169,c_1499])).

tff(c_1514,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1511])).

tff(c_1532,plain,(
    ! [E_238,B_234,A_233,C_235,D_236,F_237] :
      ( k1_partfun1(A_233,B_234,C_235,D_236,E_238,F_237) = k5_relat_1(E_238,F_237)
      | ~ m1_subset_1(F_237,k1_zfmisc_1(k2_zfmisc_1(C_235,D_236)))
      | ~ v1_funct_1(F_237)
      | ~ m1_subset_1(E_238,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_1(E_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1538,plain,(
    ! [A_233,B_234,E_238] :
      ( k1_partfun1(A_233,B_234,'#skF_2','#skF_1',E_238,'#skF_4') = k5_relat_1(E_238,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_238,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_1(E_238) ) ),
    inference(resolution,[status(thm)],[c_70,c_1532])).

tff(c_1870,plain,(
    ! [A_260,B_261,E_262] :
      ( k1_partfun1(A_260,B_261,'#skF_2','#skF_1',E_262,'#skF_4') = k5_relat_1(E_262,'#skF_4')
      | ~ m1_subset_1(E_262,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261)))
      | ~ v1_funct_1(E_262) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1538])).

tff(c_1885,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1870])).

tff(c_1899,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_588,c_1885])).

tff(c_1901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1514,c_1899])).

tff(c_1902,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1511])).

tff(c_18,plain,(
    ! [A_14] :
      ( k2_funct_1(k2_funct_1(A_14)) = A_14
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1908,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1902,c_18])).

tff(c_1912,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_74,c_1492,c_1908])).

tff(c_1914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1912])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.46/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.92  
% 4.46/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.92  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.46/1.92  
% 4.46/1.92  %Foreground sorts:
% 4.46/1.92  
% 4.46/1.92  
% 4.46/1.92  %Background operators:
% 4.46/1.92  
% 4.46/1.92  
% 4.46/1.92  %Foreground operators:
% 4.46/1.92  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.46/1.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.46/1.92  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.46/1.92  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.46/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.46/1.92  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.46/1.92  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.46/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.46/1.92  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.46/1.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.46/1.92  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.46/1.92  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.46/1.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.46/1.92  tff('#skF_2', type, '#skF_2': $i).
% 4.46/1.92  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.46/1.92  tff('#skF_3', type, '#skF_3': $i).
% 4.46/1.92  tff('#skF_1', type, '#skF_1': $i).
% 4.46/1.92  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.46/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.46/1.92  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.46/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.46/1.92  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.46/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.46/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.46/1.92  tff('#skF_4', type, '#skF_4': $i).
% 4.46/1.92  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.46/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.46/1.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.46/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.46/1.92  
% 4.83/1.94  tff(f_195, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.83/1.94  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.83/1.94  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.83/1.94  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.83/1.94  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 4.83/1.94  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.83/1.94  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.83/1.94  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 4.83/1.94  tff(f_152, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.83/1.94  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 4.83/1.94  tff(f_140, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.83/1.94  tff(f_100, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.83/1.94  tff(f_136, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.83/1.94  tff(f_169, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.83/1.94  tff(f_42, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.83/1.94  tff(f_150, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.83/1.94  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 4.83/1.94  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 4.83/1.94  tff(c_58, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.83/1.94  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.83/1.94  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.83/1.94  tff(c_102, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.83/1.94  tff(c_111, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_102])).
% 4.83/1.94  tff(c_120, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_111])).
% 4.83/1.94  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.83/1.94  tff(c_62, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.83/1.94  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.83/1.94  tff(c_199, plain, (![A_72, B_73, C_74, D_75]: (k8_relset_1(A_72, B_73, C_74, D_75)=k10_relat_1(C_74, D_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.83/1.94  tff(c_208, plain, (![D_75]: (k8_relset_1('#skF_2', '#skF_1', '#skF_4', D_75)=k10_relat_1('#skF_4', D_75))), inference(resolution, [status(thm)], [c_70, c_199])).
% 4.83/1.94  tff(c_257, plain, (![A_86, B_87, C_88]: (k8_relset_1(A_86, B_87, C_88, B_87)=k1_relset_1(A_86, B_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.83/1.94  tff(c_263, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_257])).
% 4.83/1.94  tff(c_269, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k10_relat_1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_263])).
% 4.83/1.94  tff(c_299, plain, (![B_92, A_93, C_94]: (k1_xboole_0=B_92 | k1_relset_1(A_93, B_92, C_94)=A_93 | ~v1_funct_2(C_94, A_93, B_92) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.83/1.94  tff(c_308, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_299])).
% 4.83/1.94  tff(c_316, plain, (k1_xboole_0='#skF_1' | k10_relat_1('#skF_4', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_269, c_308])).
% 4.83/1.94  tff(c_317, plain, (k10_relat_1('#skF_4', '#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_62, c_316])).
% 4.83/1.94  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.83/1.94  tff(c_108, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_102])).
% 4.83/1.94  tff(c_117, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_108])).
% 4.83/1.94  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.83/1.94  tff(c_64, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.83/1.94  tff(c_60, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.83/1.94  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.83/1.94  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.83/1.94  tff(c_157, plain, (![A_66, B_67, C_68]: (k2_relset_1(A_66, B_67, C_68)=k2_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.83/1.94  tff(c_163, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_157])).
% 4.83/1.94  tff(c_169, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_163])).
% 4.83/1.94  tff(c_6, plain, (![A_6]: (k10_relat_1(A_6, k2_relat_1(A_6))=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.83/1.94  tff(c_174, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_169, c_6])).
% 4.83/1.94  tff(c_178, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_174])).
% 4.83/1.94  tff(c_207, plain, (![D_75]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_75)=k10_relat_1('#skF_3', D_75))), inference(resolution, [status(thm)], [c_76, c_199])).
% 4.83/1.94  tff(c_261, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_257])).
% 4.83/1.94  tff(c_267, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_207, c_261])).
% 4.83/1.94  tff(c_305, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_299])).
% 4.83/1.94  tff(c_312, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_267, c_305])).
% 4.83/1.94  tff(c_313, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_60, c_312])).
% 4.83/1.94  tff(c_54, plain, (![A_45]: (k6_relat_1(A_45)=k6_partfun1(A_45))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.83/1.94  tff(c_16, plain, (![A_11, B_13]: (k2_funct_1(A_11)=B_13 | k6_relat_1(k2_relat_1(A_11))!=k5_relat_1(B_13, A_11) | k2_relat_1(B_13)!=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.83/1.94  tff(c_597, plain, (![A_145, B_146]: (k2_funct_1(A_145)=B_146 | k6_partfun1(k2_relat_1(A_145))!=k5_relat_1(B_146, A_145) | k2_relat_1(B_146)!=k1_relat_1(A_145) | ~v2_funct_1(A_145) | ~v1_funct_1(B_146) | ~v1_relat_1(B_146) | ~v1_funct_1(A_145) | ~v1_relat_1(A_145))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_16])).
% 4.83/1.94  tff(c_599, plain, (![B_146]: (k2_funct_1('#skF_3')=B_146 | k5_relat_1(B_146, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_146)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_146) | ~v1_relat_1(B_146) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_169, c_597])).
% 4.83/1.94  tff(c_602, plain, (![B_147]: (k2_funct_1('#skF_3')=B_147 | k5_relat_1(B_147, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_147)!='#skF_1' | ~v1_funct_1(B_147) | ~v1_relat_1(B_147))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_80, c_64, c_313, c_599])).
% 4.83/1.94  tff(c_605, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_120, c_602])).
% 4.83/1.94  tff(c_617, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_605])).
% 4.83/1.94  tff(c_618, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_58, c_617])).
% 4.83/1.94  tff(c_624, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_618])).
% 4.83/1.94  tff(c_50, plain, (![A_38]: (m1_subset_1(k6_partfun1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.83/1.94  tff(c_147, plain, (![A_63, B_64, D_65]: (r2_relset_1(A_63, B_64, D_65, D_65) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.83/1.94  tff(c_154, plain, (![A_38]: (r2_relset_1(A_38, A_38, k6_partfun1(A_38), k6_partfun1(A_38)))), inference(resolution, [status(thm)], [c_50, c_147])).
% 4.83/1.94  tff(c_170, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_157])).
% 4.83/1.94  tff(c_530, plain, (![B_140, F_141, D_144, A_143, E_139, C_142]: (m1_subset_1(k1_partfun1(A_143, B_140, C_142, D_144, E_139, F_141), k1_zfmisc_1(k2_zfmisc_1(A_143, D_144))) | ~m1_subset_1(F_141, k1_zfmisc_1(k2_zfmisc_1(C_142, D_144))) | ~v1_funct_1(F_141) | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(A_143, B_140))) | ~v1_funct_1(E_139))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.83/1.94  tff(c_66, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.83/1.94  tff(c_393, plain, (![D_106, C_107, A_108, B_109]: (D_106=C_107 | ~r2_relset_1(A_108, B_109, C_107, D_106) | ~m1_subset_1(D_106, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.83/1.94  tff(c_401, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_393])).
% 4.83/1.94  tff(c_416, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_401])).
% 4.83/1.94  tff(c_417, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_416])).
% 4.83/1.94  tff(c_546, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_530, c_417])).
% 4.83/1.94  tff(c_587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_546])).
% 4.83/1.94  tff(c_588, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_416])).
% 4.83/1.94  tff(c_972, plain, (![A_179, B_180, C_181, D_182]: (k2_relset_1(A_179, B_180, C_181)=B_180 | ~r2_relset_1(B_180, B_180, k1_partfun1(B_180, A_179, A_179, B_180, D_182, C_181), k6_partfun1(B_180)) | ~m1_subset_1(D_182, k1_zfmisc_1(k2_zfmisc_1(B_180, A_179))) | ~v1_funct_2(D_182, B_180, A_179) | ~v1_funct_1(D_182) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))) | ~v1_funct_2(C_181, A_179, B_180) | ~v1_funct_1(C_181))), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.83/1.94  tff(c_975, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_588, c_972])).
% 4.83/1.94  tff(c_977, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_80, c_78, c_76, c_154, c_170, c_975])).
% 4.83/1.94  tff(c_979, plain, $false, inference(negUnitSimplification, [status(thm)], [c_624, c_977])).
% 4.83/1.94  tff(c_981, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_618])).
% 4.83/1.94  tff(c_989, plain, (k10_relat_1('#skF_4', '#skF_1')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_981, c_6])).
% 4.83/1.94  tff(c_995, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_317, c_989])).
% 4.83/1.94  tff(c_81, plain, (![A_11, B_13]: (k2_funct_1(A_11)=B_13 | k6_partfun1(k2_relat_1(A_11))!=k5_relat_1(B_13, A_11) | k2_relat_1(B_13)!=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_16])).
% 4.83/1.94  tff(c_986, plain, (![B_13]: (k2_funct_1('#skF_4')=B_13 | k5_relat_1(B_13, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_13)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_981, c_81])).
% 4.83/1.94  tff(c_993, plain, (![B_13]: (k2_funct_1('#skF_4')=B_13 | k5_relat_1(B_13, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_13)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_74, c_986])).
% 4.83/1.94  tff(c_1011, plain, (![B_13]: (k2_funct_1('#skF_4')=B_13 | k5_relat_1(B_13, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_13)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_995, c_993])).
% 4.83/1.94  tff(c_1012, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1011])).
% 4.83/1.94  tff(c_10, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.83/1.94  tff(c_82, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_10])).
% 4.83/1.94  tff(c_1067, plain, (![C_199, A_197, F_201, D_200, E_202, B_198]: (k1_partfun1(A_197, B_198, C_199, D_200, E_202, F_201)=k5_relat_1(E_202, F_201) | ~m1_subset_1(F_201, k1_zfmisc_1(k2_zfmisc_1(C_199, D_200))) | ~v1_funct_1(F_201) | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~v1_funct_1(E_202))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.83/1.94  tff(c_1073, plain, (![A_197, B_198, E_202]: (k1_partfun1(A_197, B_198, '#skF_2', '#skF_1', E_202, '#skF_4')=k5_relat_1(E_202, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~v1_funct_1(E_202))), inference(resolution, [status(thm)], [c_70, c_1067])).
% 4.83/1.94  tff(c_1439, plain, (![A_218, B_219, E_220]: (k1_partfun1(A_218, B_219, '#skF_2', '#skF_1', E_220, '#skF_4')=k5_relat_1(E_220, '#skF_4') | ~m1_subset_1(E_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))) | ~v1_funct_1(E_220))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1073])).
% 4.83/1.94  tff(c_1457, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_1439])).
% 4.83/1.94  tff(c_1474, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_588, c_1457])).
% 4.83/1.94  tff(c_12, plain, (![A_8, B_10]: (v2_funct_1(A_8) | k2_relat_1(B_10)!=k1_relat_1(A_8) | ~v2_funct_1(k5_relat_1(B_10, A_8)) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.83/1.94  tff(c_1481, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1474, c_12])).
% 4.83/1.94  tff(c_1488, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_74, c_117, c_80, c_82, c_995, c_169, c_1481])).
% 4.83/1.94  tff(c_1490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1012, c_1488])).
% 4.83/1.94  tff(c_1492, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1011])).
% 4.83/1.94  tff(c_1493, plain, (![B_221]: (k2_funct_1('#skF_4')=B_221 | k5_relat_1(B_221, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_221)!='#skF_2' | ~v1_funct_1(B_221) | ~v1_relat_1(B_221))), inference(splitRight, [status(thm)], [c_1011])).
% 4.83/1.94  tff(c_1499, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_117, c_1493])).
% 4.83/1.94  tff(c_1511, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_169, c_1499])).
% 4.83/1.94  tff(c_1514, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1511])).
% 4.83/1.94  tff(c_1532, plain, (![E_238, B_234, A_233, C_235, D_236, F_237]: (k1_partfun1(A_233, B_234, C_235, D_236, E_238, F_237)=k5_relat_1(E_238, F_237) | ~m1_subset_1(F_237, k1_zfmisc_1(k2_zfmisc_1(C_235, D_236))) | ~v1_funct_1(F_237) | ~m1_subset_1(E_238, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_1(E_238))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.83/1.94  tff(c_1538, plain, (![A_233, B_234, E_238]: (k1_partfun1(A_233, B_234, '#skF_2', '#skF_1', E_238, '#skF_4')=k5_relat_1(E_238, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_238, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_1(E_238))), inference(resolution, [status(thm)], [c_70, c_1532])).
% 4.83/1.94  tff(c_1870, plain, (![A_260, B_261, E_262]: (k1_partfun1(A_260, B_261, '#skF_2', '#skF_1', E_262, '#skF_4')=k5_relat_1(E_262, '#skF_4') | ~m1_subset_1(E_262, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))) | ~v1_funct_1(E_262))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1538])).
% 4.83/1.94  tff(c_1885, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_1870])).
% 4.83/1.94  tff(c_1899, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_588, c_1885])).
% 4.83/1.94  tff(c_1901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1514, c_1899])).
% 4.83/1.94  tff(c_1902, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1511])).
% 4.83/1.94  tff(c_18, plain, (![A_14]: (k2_funct_1(k2_funct_1(A_14))=A_14 | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.83/1.94  tff(c_1908, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1902, c_18])).
% 4.83/1.94  tff(c_1912, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_74, c_1492, c_1908])).
% 4.83/1.94  tff(c_1914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1912])).
% 4.83/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.83/1.94  
% 4.83/1.94  Inference rules
% 4.83/1.94  ----------------------
% 4.83/1.94  #Ref     : 0
% 4.83/1.94  #Sup     : 401
% 4.83/1.94  #Fact    : 0
% 4.83/1.94  #Define  : 0
% 4.83/1.94  #Split   : 18
% 4.83/1.94  #Chain   : 0
% 4.83/1.94  #Close   : 0
% 4.83/1.94  
% 4.83/1.95  Ordering : KBO
% 4.83/1.95  
% 4.83/1.95  Simplification rules
% 4.83/1.95  ----------------------
% 4.83/1.95  #Subsume      : 2
% 4.83/1.95  #Demod        : 292
% 4.83/1.95  #Tautology    : 101
% 4.83/1.95  #SimpNegUnit  : 25
% 4.83/1.95  #BackRed      : 13
% 4.83/1.95  
% 4.83/1.95  #Partial instantiations: 0
% 4.83/1.95  #Strategies tried      : 1
% 4.83/1.95  
% 4.83/1.95  Timing (in seconds)
% 4.83/1.95  ----------------------
% 4.83/1.95  Preprocessing        : 0.38
% 4.83/1.95  Parsing              : 0.22
% 4.83/1.95  CNF conversion       : 0.02
% 4.83/1.95  Main loop            : 0.73
% 4.83/1.95  Inferencing          : 0.27
% 4.83/1.95  Reduction            : 0.24
% 4.83/1.95  Demodulation         : 0.17
% 4.83/1.95  BG Simplification    : 0.04
% 4.83/1.95  Subsumption          : 0.12
% 4.83/1.95  Abstraction          : 0.04
% 4.83/1.95  MUC search           : 0.00
% 4.83/1.95  Cooper               : 0.00
% 4.83/1.95  Total                : 1.16
% 4.83/1.95  Index Insertion      : 0.00
% 4.83/1.95  Index Deletion       : 0.00
% 4.83/1.95  Index Matching       : 0.00
% 4.83/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
