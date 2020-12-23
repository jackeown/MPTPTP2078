%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:05 EST 2020

% Result     : Theorem 7.04s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :  184 (1041 expanded)
%              Number of leaves         :   47 ( 390 expanded)
%              Depth                    :   24
%              Number of atoms          :  394 (4388 expanded)
%              Number of equality atoms :  143 (1438 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_214,negated_conjecture,(
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

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_129,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_127,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_113,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_117,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_188,axiom,(
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

tff(f_146,axiom,(
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

tff(f_172,axiom,(
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

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_62,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_139,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_152,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_139])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_46,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_24,plain,(
    ! [A_16] : v2_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_85,plain,(
    ! [A_16] : v2_funct_1(k6_partfun1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_24])).

tff(c_84,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_806,plain,(
    ! [F_112,A_111,D_115,B_116,E_114,C_113] :
      ( k1_partfun1(A_111,B_116,C_113,D_115,E_114,F_112) = k5_relat_1(E_114,F_112)
      | ~ m1_subset_1(F_112,k1_zfmisc_1(k2_zfmisc_1(C_113,D_115)))
      | ~ v1_funct_1(F_112)
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_111,B_116)))
      | ~ v1_funct_1(E_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_812,plain,(
    ! [A_111,B_116,E_114] :
      ( k1_partfun1(A_111,B_116,'#skF_2','#skF_1',E_114,'#skF_4') = k5_relat_1(E_114,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_111,B_116)))
      | ~ v1_funct_1(E_114) ) ),
    inference(resolution,[status(thm)],[c_74,c_806])).

tff(c_1906,plain,(
    ! [A_173,B_174,E_175] :
      ( k1_partfun1(A_173,B_174,'#skF_2','#skF_1',E_175,'#skF_4') = k5_relat_1(E_175,'#skF_4')
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_1(E_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_812])).

tff(c_1912,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1906])).

tff(c_1919,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1912])).

tff(c_1939,plain,(
    ! [B_180,E_177,A_178,D_181,F_176,C_179] :
      ( m1_subset_1(k1_partfun1(A_178,B_180,C_179,D_181,E_177,F_176),k1_zfmisc_1(k2_zfmisc_1(A_178,D_181)))
      | ~ m1_subset_1(F_176,k1_zfmisc_1(k2_zfmisc_1(C_179,D_181)))
      | ~ v1_funct_1(F_176)
      | ~ m1_subset_1(E_177,k1_zfmisc_1(k2_zfmisc_1(A_178,B_180)))
      | ~ v1_funct_1(E_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1970,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1919,c_1939])).

tff(c_1984,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_1970])).

tff(c_42,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_452,plain,(
    ! [D_91,C_92,A_93,B_94] :
      ( D_91 = C_92
      | ~ r2_relset_1(A_93,B_94,C_92,D_91)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_460,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_452])).

tff(c_475,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_460])).

tff(c_3445,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1984,c_1919,c_1919,c_475])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_76,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_289,plain,(
    ! [A_82,B_83,C_84] :
      ( k2_relset_1(A_82,B_83,C_84) = k2_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_302,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_289])).

tff(c_1071,plain,(
    ! [A_127,C_128,B_129] :
      ( k6_partfun1(A_127) = k5_relat_1(C_128,k2_funct_1(C_128))
      | k1_xboole_0 = B_129
      | ~ v2_funct_1(C_128)
      | k2_relset_1(A_127,B_129,C_128) != B_129
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_127,B_129)))
      | ~ v1_funct_2(C_128,A_127,B_129)
      | ~ v1_funct_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1077,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_1071])).

tff(c_1087,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_302,c_1077])).

tff(c_1088,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1087])).

tff(c_1153,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1088])).

tff(c_82,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_1393,plain,(
    ! [A_144,B_145,E_146] :
      ( k1_partfun1(A_144,B_145,'#skF_2','#skF_1',E_146,'#skF_4') = k5_relat_1(E_146,'#skF_4')
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ v1_funct_1(E_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_812])).

tff(c_1402,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1393])).

tff(c_1410,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1402])).

tff(c_1618,plain,(
    r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_70])).

tff(c_1787,plain,(
    ! [A_166,B_167,C_168,D_169] :
      ( k2_relset_1(A_166,B_167,C_168) = B_167
      | ~ r2_relset_1(B_167,B_167,k1_partfun1(B_167,A_166,A_166,B_167,D_169,C_168),k6_partfun1(B_167))
      | ~ m1_subset_1(D_169,k1_zfmisc_1(k2_zfmisc_1(B_167,A_166)))
      | ~ v1_funct_2(D_169,B_167,A_166)
      | ~ v1_funct_1(D_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ v1_funct_2(C_168,A_166,B_167)
      | ~ v1_funct_1(C_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1790,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1410,c_1787])).

tff(c_1795,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_84,c_82,c_80,c_1618,c_302,c_1790])).

tff(c_1797,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1153,c_1795])).

tff(c_1798,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1088])).

tff(c_1843,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1798])).

tff(c_72,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_2417,plain,(
    ! [A_200,C_204,D_201,B_203,E_202] :
      ( k1_xboole_0 = C_204
      | v2_funct_1(E_202)
      | k2_relset_1(A_200,B_203,D_201) != B_203
      | ~ v2_funct_1(k1_partfun1(A_200,B_203,B_203,C_204,D_201,E_202))
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(B_203,C_204)))
      | ~ v1_funct_2(E_202,B_203,C_204)
      | ~ v1_funct_1(E_202)
      | ~ m1_subset_1(D_201,k1_zfmisc_1(k2_zfmisc_1(A_200,B_203)))
      | ~ v1_funct_2(D_201,A_200,B_203)
      | ~ v1_funct_1(D_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_2419,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1919,c_2417])).

tff(c_2421,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_2419])).

tff(c_2422,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1843,c_66,c_2421])).

tff(c_3446,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3445,c_2422])).

tff(c_3459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_3446])).

tff(c_3461,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1798])).

tff(c_16,plain,(
    ! [A_14] :
      ( k4_relat_1(A_14) = k2_funct_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3464,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3461,c_16])).

tff(c_3467,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_78,c_3464])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3483,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3467,c_2])).

tff(c_3495,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_3483])).

tff(c_1799,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1088])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_relat_1(k4_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3477,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3467,c_6])).

tff(c_3491,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_1799,c_3477])).

tff(c_14,plain,(
    ! [A_13] :
      ( k7_relat_1(A_13,k1_relat_1(A_13)) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3520,plain,
    ( k7_relat_1(k2_funct_1('#skF_4'),'#skF_1') = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3491,c_14])).

tff(c_3526,plain,(
    k7_relat_1(k2_funct_1('#skF_4'),'#skF_1') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3495,c_3520])).

tff(c_151,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_139])).

tff(c_295,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_289])).

tff(c_301,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_295])).

tff(c_10,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_relat_1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_88,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_partfun1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_308,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_88])).

tff(c_312,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_308])).

tff(c_68,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_195,plain,(
    ! [A_75] :
      ( k4_relat_1(A_75) = k2_funct_1(A_75)
      | ~ v2_funct_1(A_75)
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_201,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_195])).

tff(c_207,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_84,c_201])).

tff(c_217,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_2])).

tff(c_225,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_217])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_3571,plain,(
    ! [B_225,C_226,A_227] :
      ( k6_partfun1(B_225) = k5_relat_1(k2_funct_1(C_226),C_226)
      | k1_xboole_0 = B_225
      | ~ v2_funct_1(C_226)
      | k2_relset_1(A_227,B_225,C_226) != B_225
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_227,B_225)))
      | ~ v1_funct_2(C_226,A_227,B_225)
      | ~ v1_funct_1(C_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_3575,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_3571])).

tff(c_3583,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_72,c_68,c_3575])).

tff(c_3584,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3583])).

tff(c_211,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_6])).

tff(c_221,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_211])).

tff(c_304,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_221])).

tff(c_22,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_86,plain,(
    ! [A_16] : v1_relat_1(k6_partfun1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_22])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k5_relat_1(k6_relat_1(A_11),B_12) = k7_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_87,plain,(
    ! [A_11,B_12] :
      ( k5_relat_1(k6_partfun1(A_11),B_12) = k7_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_314,plain,(
    ! [A_85,B_86,C_87] :
      ( k5_relat_1(k5_relat_1(A_85,B_86),C_87) = k5_relat_1(A_85,k5_relat_1(B_86,C_87))
      | ~ v1_relat_1(C_87)
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_336,plain,(
    ! [A_11,B_12,C_87] :
      ( k5_relat_1(k6_partfun1(A_11),k5_relat_1(B_12,C_87)) = k5_relat_1(k7_relat_1(B_12,A_11),C_87)
      | ~ v1_relat_1(C_87)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(k6_partfun1(A_11))
      | ~ v1_relat_1(B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_314])).

tff(c_351,plain,(
    ! [A_11,B_12,C_87] :
      ( k5_relat_1(k6_partfun1(A_11),k5_relat_1(B_12,C_87)) = k5_relat_1(k7_relat_1(B_12,A_11),C_87)
      | ~ v1_relat_1(C_87)
      | ~ v1_relat_1(B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_336])).

tff(c_3592,plain,(
    ! [A_11] :
      ( k5_relat_1(k7_relat_1(k2_funct_1('#skF_3'),A_11),'#skF_3') = k5_relat_1(k6_partfun1(A_11),k6_partfun1('#skF_2'))
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3584,c_351])).

tff(c_3903,plain,(
    ! [A_243] : k5_relat_1(k7_relat_1(k2_funct_1('#skF_3'),A_243),'#skF_3') = k5_relat_1(k6_partfun1(A_243),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_151,c_3592])).

tff(c_3922,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))),k6_partfun1('#skF_2')) = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3903])).

tff(c_3931,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_3584,c_304,c_3922])).

tff(c_230,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_14])).

tff(c_234,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_230])).

tff(c_303,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_234])).

tff(c_4159,plain,(
    ! [A_257,B_258,E_259] :
      ( k1_partfun1(A_257,B_258,'#skF_2','#skF_1',E_259,'#skF_4') = k5_relat_1(E_259,'#skF_4')
      | ~ m1_subset_1(E_259,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258)))
      | ~ v1_funct_1(E_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_812])).

tff(c_4174,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_4159])).

tff(c_4188,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4174])).

tff(c_36,plain,(
    ! [C_30,E_32,D_31,B_29,F_33,A_28] :
      ( m1_subset_1(k1_partfun1(A_28,B_29,C_30,D_31,E_32,F_33),k1_zfmisc_1(k2_zfmisc_1(A_28,D_31)))
      | ~ m1_subset_1(F_33,k1_zfmisc_1(k2_zfmisc_1(C_30,D_31)))
      | ~ v1_funct_1(F_33)
      | ~ m1_subset_1(E_32,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1(E_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4201,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4188,c_36])).

tff(c_4211,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_4201])).

tff(c_5068,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4211,c_4188,c_4188,c_475])).

tff(c_8,plain,(
    ! [A_3,B_7,C_9] :
      ( k5_relat_1(k5_relat_1(A_3,B_7),C_9) = k5_relat_1(A_3,k5_relat_1(B_7,C_9))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3595,plain,(
    ! [C_9] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_9)) = k5_relat_1(k6_partfun1('#skF_2'),C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3584,c_8])).

tff(c_5397,plain,(
    ! [C_278] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_278)) = k5_relat_1(k6_partfun1('#skF_2'),C_278)
      | ~ v1_relat_1(C_278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_151,c_3595])).

tff(c_5419,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5068,c_5397])).

tff(c_5487,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_5419])).

tff(c_1075,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1071])).

tff(c_1083,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_72,c_68,c_1075])).

tff(c_1084,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1083])).

tff(c_5439,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1084,c_5397])).

tff(c_5495,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_5439])).

tff(c_5583,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5487,c_5495])).

tff(c_5599,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5583,c_87])).

tff(c_5614,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_303,c_5599])).

tff(c_5635,plain,
    ( k7_relat_1('#skF_4','#skF_2') = k2_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5614,c_87])).

tff(c_5650,plain,(
    k7_relat_1('#skF_4','#skF_2') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_5635])).

tff(c_3460,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1798])).

tff(c_3556,plain,(
    ! [A_11] :
      ( k5_relat_1(k7_relat_1('#skF_4',A_11),k2_funct_1('#skF_4')) = k5_relat_1(k6_partfun1(A_11),k6_partfun1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3460,c_351])).

tff(c_3563,plain,(
    ! [A_11] : k5_relat_1(k7_relat_1('#skF_4',A_11),k2_funct_1('#skF_4')) = k5_relat_1(k6_partfun1(A_11),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_3495,c_3556])).

tff(c_5657,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) = k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5650,c_3563])).

tff(c_5666,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3931,c_5657])).

tff(c_1095,plain,(
    ! [C_9] :
      ( k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),C_9)) = k5_relat_1(k6_partfun1('#skF_1'),C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1084,c_8])).

tff(c_1101,plain,(
    ! [C_9] :
      ( k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),C_9)) = k5_relat_1(k6_partfun1('#skF_1'),C_9)
      | ~ v1_relat_1(C_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_225,c_1095])).

tff(c_5906,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k5_relat_1('#skF_3',k6_partfun1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5666,c_1101])).

tff(c_5919,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3495,c_312,c_5906])).

tff(c_5981,plain,
    ( k7_relat_1(k2_funct_1('#skF_4'),'#skF_1') = '#skF_3'
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5919,c_87])).

tff(c_5996,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3495,c_3526,c_5981])).

tff(c_26,plain,(
    ! [A_17] :
      ( k2_funct_1(k2_funct_1(A_17)) = A_17
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6022,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5996,c_26])).

tff(c_6032,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_78,c_3461,c_6022])).

tff(c_6034,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_6032])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:46:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.04/2.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.04/2.51  
% 7.04/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.04/2.51  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.04/2.51  
% 7.04/2.51  %Foreground sorts:
% 7.04/2.51  
% 7.04/2.51  
% 7.04/2.51  %Background operators:
% 7.04/2.51  
% 7.04/2.51  
% 7.04/2.51  %Foreground operators:
% 7.04/2.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.04/2.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.04/2.51  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.04/2.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.04/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.04/2.51  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.04/2.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.04/2.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.04/2.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.04/2.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.04/2.51  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.04/2.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.04/2.51  tff('#skF_2', type, '#skF_2': $i).
% 7.04/2.51  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.04/2.51  tff('#skF_3', type, '#skF_3': $i).
% 7.04/2.51  tff('#skF_1', type, '#skF_1': $i).
% 7.04/2.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.04/2.51  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.04/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.04/2.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.04/2.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.04/2.51  tff('#skF_4', type, '#skF_4': $i).
% 7.04/2.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.04/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.04/2.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.04/2.51  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 7.04/2.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.04/2.51  
% 7.31/2.54  tff(f_214, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 7.31/2.54  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.31/2.54  tff(f_129, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.31/2.54  tff(f_77, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.31/2.54  tff(f_127, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.31/2.54  tff(f_113, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.31/2.54  tff(f_117, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.31/2.54  tff(f_101, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.31/2.54  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.31/2.54  tff(f_188, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 7.31/2.54  tff(f_146, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.31/2.54  tff(f_172, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 7.31/2.54  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 7.31/2.54  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 7.31/2.54  tff(f_35, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 7.31/2.54  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 7.31/2.54  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 7.31/2.54  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 7.31/2.54  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 7.31/2.54  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 7.31/2.54  tff(c_62, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_214])).
% 7.31/2.54  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_214])).
% 7.31/2.54  tff(c_139, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.31/2.54  tff(c_152, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_139])).
% 7.31/2.54  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_214])).
% 7.31/2.54  tff(c_46, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.31/2.54  tff(c_24, plain, (![A_16]: (v2_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.31/2.54  tff(c_85, plain, (![A_16]: (v2_funct_1(k6_partfun1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_24])).
% 7.31/2.54  tff(c_84, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_214])).
% 7.31/2.54  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_214])).
% 7.31/2.54  tff(c_806, plain, (![F_112, A_111, D_115, B_116, E_114, C_113]: (k1_partfun1(A_111, B_116, C_113, D_115, E_114, F_112)=k5_relat_1(E_114, F_112) | ~m1_subset_1(F_112, k1_zfmisc_1(k2_zfmisc_1(C_113, D_115))) | ~v1_funct_1(F_112) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_111, B_116))) | ~v1_funct_1(E_114))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.31/2.54  tff(c_812, plain, (![A_111, B_116, E_114]: (k1_partfun1(A_111, B_116, '#skF_2', '#skF_1', E_114, '#skF_4')=k5_relat_1(E_114, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_111, B_116))) | ~v1_funct_1(E_114))), inference(resolution, [status(thm)], [c_74, c_806])).
% 7.31/2.54  tff(c_1906, plain, (![A_173, B_174, E_175]: (k1_partfun1(A_173, B_174, '#skF_2', '#skF_1', E_175, '#skF_4')=k5_relat_1(E_175, '#skF_4') | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~v1_funct_1(E_175))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_812])).
% 7.31/2.54  tff(c_1912, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_1906])).
% 7.31/2.54  tff(c_1919, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1912])).
% 7.31/2.54  tff(c_1939, plain, (![B_180, E_177, A_178, D_181, F_176, C_179]: (m1_subset_1(k1_partfun1(A_178, B_180, C_179, D_181, E_177, F_176), k1_zfmisc_1(k2_zfmisc_1(A_178, D_181))) | ~m1_subset_1(F_176, k1_zfmisc_1(k2_zfmisc_1(C_179, D_181))) | ~v1_funct_1(F_176) | ~m1_subset_1(E_177, k1_zfmisc_1(k2_zfmisc_1(A_178, B_180))) | ~v1_funct_1(E_177))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.31/2.54  tff(c_1970, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1919, c_1939])).
% 7.31/2.54  tff(c_1984, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_1970])).
% 7.31/2.54  tff(c_42, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.31/2.54  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_214])).
% 7.31/2.54  tff(c_452, plain, (![D_91, C_92, A_93, B_94]: (D_91=C_92 | ~r2_relset_1(A_93, B_94, C_92, D_91) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.31/2.54  tff(c_460, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_452])).
% 7.31/2.54  tff(c_475, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_460])).
% 7.31/2.54  tff(c_3445, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1984, c_1919, c_1919, c_475])).
% 7.31/2.54  tff(c_66, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_214])).
% 7.31/2.54  tff(c_76, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_214])).
% 7.31/2.54  tff(c_289, plain, (![A_82, B_83, C_84]: (k2_relset_1(A_82, B_83, C_84)=k2_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.31/2.54  tff(c_302, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_289])).
% 7.31/2.54  tff(c_1071, plain, (![A_127, C_128, B_129]: (k6_partfun1(A_127)=k5_relat_1(C_128, k2_funct_1(C_128)) | k1_xboole_0=B_129 | ~v2_funct_1(C_128) | k2_relset_1(A_127, B_129, C_128)!=B_129 | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_127, B_129))) | ~v1_funct_2(C_128, A_127, B_129) | ~v1_funct_1(C_128))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.31/2.54  tff(c_1077, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_1071])).
% 7.31/2.54  tff(c_1087, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_302, c_1077])).
% 7.31/2.54  tff(c_1088, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_66, c_1087])).
% 7.31/2.54  tff(c_1153, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1088])).
% 7.31/2.54  tff(c_82, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_214])).
% 7.31/2.54  tff(c_1393, plain, (![A_144, B_145, E_146]: (k1_partfun1(A_144, B_145, '#skF_2', '#skF_1', E_146, '#skF_4')=k5_relat_1(E_146, '#skF_4') | ~m1_subset_1(E_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~v1_funct_1(E_146))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_812])).
% 7.31/2.54  tff(c_1402, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_1393])).
% 7.31/2.54  tff(c_1410, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1402])).
% 7.31/2.54  tff(c_1618, plain, (r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1410, c_70])).
% 7.31/2.54  tff(c_1787, plain, (![A_166, B_167, C_168, D_169]: (k2_relset_1(A_166, B_167, C_168)=B_167 | ~r2_relset_1(B_167, B_167, k1_partfun1(B_167, A_166, A_166, B_167, D_169, C_168), k6_partfun1(B_167)) | ~m1_subset_1(D_169, k1_zfmisc_1(k2_zfmisc_1(B_167, A_166))) | ~v1_funct_2(D_169, B_167, A_166) | ~v1_funct_1(D_169) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~v1_funct_2(C_168, A_166, B_167) | ~v1_funct_1(C_168))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.31/2.54  tff(c_1790, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1410, c_1787])).
% 7.31/2.54  tff(c_1795, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_84, c_82, c_80, c_1618, c_302, c_1790])).
% 7.31/2.54  tff(c_1797, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1153, c_1795])).
% 7.31/2.54  tff(c_1798, plain, (~v2_funct_1('#skF_4') | k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1088])).
% 7.31/2.54  tff(c_1843, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1798])).
% 7.31/2.54  tff(c_72, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_214])).
% 7.31/2.54  tff(c_2417, plain, (![A_200, C_204, D_201, B_203, E_202]: (k1_xboole_0=C_204 | v2_funct_1(E_202) | k2_relset_1(A_200, B_203, D_201)!=B_203 | ~v2_funct_1(k1_partfun1(A_200, B_203, B_203, C_204, D_201, E_202)) | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(B_203, C_204))) | ~v1_funct_2(E_202, B_203, C_204) | ~v1_funct_1(E_202) | ~m1_subset_1(D_201, k1_zfmisc_1(k2_zfmisc_1(A_200, B_203))) | ~v1_funct_2(D_201, A_200, B_203) | ~v1_funct_1(D_201))), inference(cnfTransformation, [status(thm)], [f_172])).
% 7.31/2.54  tff(c_2419, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1919, c_2417])).
% 7.31/2.54  tff(c_2421, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_2419])).
% 7.31/2.54  tff(c_2422, plain, (~v2_funct_1(k5_relat_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1843, c_66, c_2421])).
% 7.31/2.54  tff(c_3446, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3445, c_2422])).
% 7.31/2.54  tff(c_3459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_3446])).
% 7.31/2.54  tff(c_3461, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1798])).
% 7.31/2.54  tff(c_16, plain, (![A_14]: (k4_relat_1(A_14)=k2_funct_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.31/2.54  tff(c_3464, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3461, c_16])).
% 7.31/2.54  tff(c_3467, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_78, c_3464])).
% 7.31/2.54  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.31/2.54  tff(c_3483, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3467, c_2])).
% 7.31/2.54  tff(c_3495, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_3483])).
% 7.31/2.54  tff(c_1799, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_1088])).
% 7.31/2.54  tff(c_6, plain, (![A_2]: (k1_relat_1(k4_relat_1(A_2))=k2_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.31/2.54  tff(c_3477, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3467, c_6])).
% 7.31/2.54  tff(c_3491, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_1799, c_3477])).
% 7.31/2.54  tff(c_14, plain, (![A_13]: (k7_relat_1(A_13, k1_relat_1(A_13))=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.31/2.54  tff(c_3520, plain, (k7_relat_1(k2_funct_1('#skF_4'), '#skF_1')=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3491, c_14])).
% 7.31/2.54  tff(c_3526, plain, (k7_relat_1(k2_funct_1('#skF_4'), '#skF_1')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3495, c_3520])).
% 7.31/2.54  tff(c_151, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_139])).
% 7.31/2.54  tff(c_295, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_289])).
% 7.31/2.54  tff(c_301, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_295])).
% 7.31/2.54  tff(c_10, plain, (![A_10]: (k5_relat_1(A_10, k6_relat_1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.31/2.54  tff(c_88, plain, (![A_10]: (k5_relat_1(A_10, k6_partfun1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 7.31/2.54  tff(c_308, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_301, c_88])).
% 7.31/2.54  tff(c_312, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_151, c_308])).
% 7.31/2.54  tff(c_68, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_214])).
% 7.31/2.54  tff(c_195, plain, (![A_75]: (k4_relat_1(A_75)=k2_funct_1(A_75) | ~v2_funct_1(A_75) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.31/2.54  tff(c_201, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_195])).
% 7.31/2.54  tff(c_207, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_84, c_201])).
% 7.31/2.54  tff(c_217, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_207, c_2])).
% 7.31/2.54  tff(c_225, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_217])).
% 7.31/2.54  tff(c_64, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_214])).
% 7.31/2.54  tff(c_3571, plain, (![B_225, C_226, A_227]: (k6_partfun1(B_225)=k5_relat_1(k2_funct_1(C_226), C_226) | k1_xboole_0=B_225 | ~v2_funct_1(C_226) | k2_relset_1(A_227, B_225, C_226)!=B_225 | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_227, B_225))) | ~v1_funct_2(C_226, A_227, B_225) | ~v1_funct_1(C_226))), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.31/2.54  tff(c_3575, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_3571])).
% 7.31/2.54  tff(c_3583, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_72, c_68, c_3575])).
% 7.31/2.54  tff(c_3584, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_64, c_3583])).
% 7.31/2.54  tff(c_211, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_207, c_6])).
% 7.31/2.54  tff(c_221, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_211])).
% 7.31/2.54  tff(c_304, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_301, c_221])).
% 7.31/2.54  tff(c_22, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.31/2.54  tff(c_86, plain, (![A_16]: (v1_relat_1(k6_partfun1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_22])).
% 7.31/2.54  tff(c_12, plain, (![A_11, B_12]: (k5_relat_1(k6_relat_1(A_11), B_12)=k7_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.31/2.54  tff(c_87, plain, (![A_11, B_12]: (k5_relat_1(k6_partfun1(A_11), B_12)=k7_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 7.31/2.54  tff(c_314, plain, (![A_85, B_86, C_87]: (k5_relat_1(k5_relat_1(A_85, B_86), C_87)=k5_relat_1(A_85, k5_relat_1(B_86, C_87)) | ~v1_relat_1(C_87) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.31/2.54  tff(c_336, plain, (![A_11, B_12, C_87]: (k5_relat_1(k6_partfun1(A_11), k5_relat_1(B_12, C_87))=k5_relat_1(k7_relat_1(B_12, A_11), C_87) | ~v1_relat_1(C_87) | ~v1_relat_1(B_12) | ~v1_relat_1(k6_partfun1(A_11)) | ~v1_relat_1(B_12))), inference(superposition, [status(thm), theory('equality')], [c_87, c_314])).
% 7.31/2.54  tff(c_351, plain, (![A_11, B_12, C_87]: (k5_relat_1(k6_partfun1(A_11), k5_relat_1(B_12, C_87))=k5_relat_1(k7_relat_1(B_12, A_11), C_87) | ~v1_relat_1(C_87) | ~v1_relat_1(B_12))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_336])).
% 7.31/2.54  tff(c_3592, plain, (![A_11]: (k5_relat_1(k7_relat_1(k2_funct_1('#skF_3'), A_11), '#skF_3')=k5_relat_1(k6_partfun1(A_11), k6_partfun1('#skF_2')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3584, c_351])).
% 7.31/2.54  tff(c_3903, plain, (![A_243]: (k5_relat_1(k7_relat_1(k2_funct_1('#skF_3'), A_243), '#skF_3')=k5_relat_1(k6_partfun1(A_243), k6_partfun1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_151, c_3592])).
% 7.31/2.54  tff(c_3922, plain, (k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))), k6_partfun1('#skF_2'))=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3903])).
% 7.31/2.54  tff(c_3931, plain, (k5_relat_1(k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_225, c_3584, c_304, c_3922])).
% 7.31/2.54  tff(c_230, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_221, c_14])).
% 7.31/2.54  tff(c_234, plain, (k7_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_225, c_230])).
% 7.31/2.54  tff(c_303, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_301, c_234])).
% 7.31/2.54  tff(c_4159, plain, (![A_257, B_258, E_259]: (k1_partfun1(A_257, B_258, '#skF_2', '#skF_1', E_259, '#skF_4')=k5_relat_1(E_259, '#skF_4') | ~m1_subset_1(E_259, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))) | ~v1_funct_1(E_259))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_812])).
% 7.31/2.54  tff(c_4174, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_4159])).
% 7.31/2.54  tff(c_4188, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4174])).
% 7.31/2.54  tff(c_36, plain, (![C_30, E_32, D_31, B_29, F_33, A_28]: (m1_subset_1(k1_partfun1(A_28, B_29, C_30, D_31, E_32, F_33), k1_zfmisc_1(k2_zfmisc_1(A_28, D_31))) | ~m1_subset_1(F_33, k1_zfmisc_1(k2_zfmisc_1(C_30, D_31))) | ~v1_funct_1(F_33) | ~m1_subset_1(E_32, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_1(E_32))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.31/2.54  tff(c_4201, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4188, c_36])).
% 7.31/2.54  tff(c_4211, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_4201])).
% 7.31/2.54  tff(c_5068, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4211, c_4188, c_4188, c_475])).
% 7.31/2.54  tff(c_8, plain, (![A_3, B_7, C_9]: (k5_relat_1(k5_relat_1(A_3, B_7), C_9)=k5_relat_1(A_3, k5_relat_1(B_7, C_9)) | ~v1_relat_1(C_9) | ~v1_relat_1(B_7) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.31/2.54  tff(c_3595, plain, (![C_9]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_9))=k5_relat_1(k6_partfun1('#skF_2'), C_9) | ~v1_relat_1(C_9) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3584, c_8])).
% 7.31/2.54  tff(c_5397, plain, (![C_278]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_278))=k5_relat_1(k6_partfun1('#skF_2'), C_278) | ~v1_relat_1(C_278))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_151, c_3595])).
% 7.31/2.54  tff(c_5419, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5068, c_5397])).
% 7.31/2.54  tff(c_5487, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_5419])).
% 7.31/2.54  tff(c_1075, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_1071])).
% 7.31/2.54  tff(c_1083, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_72, c_68, c_1075])).
% 7.31/2.54  tff(c_1084, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_1083])).
% 7.31/2.54  tff(c_5439, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1084, c_5397])).
% 7.31/2.54  tff(c_5495, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_5439])).
% 7.31/2.54  tff(c_5583, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5487, c_5495])).
% 7.31/2.54  tff(c_5599, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5583, c_87])).
% 7.31/2.54  tff(c_5614, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_225, c_303, c_5599])).
% 7.31/2.54  tff(c_5635, plain, (k7_relat_1('#skF_4', '#skF_2')=k2_funct_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5614, c_87])).
% 7.31/2.54  tff(c_5650, plain, (k7_relat_1('#skF_4', '#skF_2')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_5635])).
% 7.31/2.54  tff(c_3460, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1798])).
% 7.31/2.54  tff(c_3556, plain, (![A_11]: (k5_relat_1(k7_relat_1('#skF_4', A_11), k2_funct_1('#skF_4'))=k5_relat_1(k6_partfun1(A_11), k6_partfun1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3460, c_351])).
% 7.31/2.54  tff(c_3563, plain, (![A_11]: (k5_relat_1(k7_relat_1('#skF_4', A_11), k2_funct_1('#skF_4'))=k5_relat_1(k6_partfun1(A_11), k6_partfun1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_3495, c_3556])).
% 7.31/2.54  tff(c_5657, plain, (k5_relat_1(k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))=k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5650, c_3563])).
% 7.31/2.54  tff(c_5666, plain, (k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3931, c_5657])).
% 7.31/2.54  tff(c_1095, plain, (![C_9]: (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), C_9))=k5_relat_1(k6_partfun1('#skF_1'), C_9) | ~v1_relat_1(C_9) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1084, c_8])).
% 7.31/2.54  tff(c_1101, plain, (![C_9]: (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), C_9))=k5_relat_1(k6_partfun1('#skF_1'), C_9) | ~v1_relat_1(C_9))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_225, c_1095])).
% 7.31/2.54  tff(c_5906, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k5_relat_1('#skF_3', k6_partfun1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5666, c_1101])).
% 7.31/2.54  tff(c_5919, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3495, c_312, c_5906])).
% 7.31/2.54  tff(c_5981, plain, (k7_relat_1(k2_funct_1('#skF_4'), '#skF_1')='#skF_3' | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5919, c_87])).
% 7.31/2.54  tff(c_5996, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3495, c_3526, c_5981])).
% 7.31/2.54  tff(c_26, plain, (![A_17]: (k2_funct_1(k2_funct_1(A_17))=A_17 | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.31/2.54  tff(c_6022, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5996, c_26])).
% 7.31/2.54  tff(c_6032, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_78, c_3461, c_6022])).
% 7.31/2.54  tff(c_6034, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_6032])).
% 7.31/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.54  
% 7.31/2.54  Inference rules
% 7.31/2.54  ----------------------
% 7.31/2.54  #Ref     : 0
% 7.31/2.54  #Sup     : 1305
% 7.31/2.54  #Fact    : 0
% 7.31/2.54  #Define  : 0
% 7.31/2.54  #Split   : 16
% 7.31/2.54  #Chain   : 0
% 7.31/2.54  #Close   : 0
% 7.31/2.54  
% 7.31/2.54  Ordering : KBO
% 7.31/2.54  
% 7.31/2.54  Simplification rules
% 7.31/2.54  ----------------------
% 7.31/2.54  #Subsume      : 21
% 7.31/2.54  #Demod        : 2018
% 7.31/2.54  #Tautology    : 545
% 7.31/2.54  #SimpNegUnit  : 48
% 7.31/2.54  #BackRed      : 60
% 7.31/2.54  
% 7.31/2.54  #Partial instantiations: 0
% 7.31/2.54  #Strategies tried      : 1
% 7.31/2.54  
% 7.31/2.54  Timing (in seconds)
% 7.31/2.54  ----------------------
% 7.31/2.54  Preprocessing        : 0.39
% 7.31/2.54  Parsing              : 0.21
% 7.31/2.54  CNF conversion       : 0.03
% 7.31/2.54  Main loop            : 1.36
% 7.31/2.54  Inferencing          : 0.43
% 7.31/2.54  Reduction            : 0.57
% 7.31/2.54  Demodulation         : 0.44
% 7.31/2.54  BG Simplification    : 0.05
% 7.31/2.54  Subsumption          : 0.22
% 7.31/2.54  Abstraction          : 0.06
% 7.31/2.54  MUC search           : 0.00
% 7.31/2.54  Cooper               : 0.00
% 7.31/2.54  Total                : 1.81
% 7.31/2.54  Index Insertion      : 0.00
% 7.31/2.54  Index Deletion       : 0.00
% 7.31/2.54  Index Matching       : 0.00
% 7.31/2.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
