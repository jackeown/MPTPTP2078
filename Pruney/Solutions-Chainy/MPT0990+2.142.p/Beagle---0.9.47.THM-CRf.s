%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:17 EST 2020

% Result     : Theorem 34.14s
% Output     : CNFRefutation 34.39s
% Verified   : 
% Statistics : Number of formulae       :  199 (2811 expanded)
%              Number of leaves         :   51 (1041 expanded)
%              Depth                    :   19
%              Number of atoms          :  483 (11407 expanded)
%              Number of equality atoms :  165 (3215 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_259,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_217,axiom,(
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

tff(f_201,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_147,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_173,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_233,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_126,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
          & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_199,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_189,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_155,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_185,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_96,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_55,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_143,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(c_88,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_6,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_106,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_196,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_205,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_106,c_196])).

tff(c_214,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_205])).

tff(c_110,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_94,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_238,plain,(
    ! [A_75] :
      ( k4_relat_1(A_75) = k2_funct_1(A_75)
      | ~ v2_funct_1(A_75)
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_244,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_238])).

tff(c_250,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_110,c_244])).

tff(c_4,plain,(
    ! [A_4] :
      ( v1_relat_1(k4_relat_1(A_4))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_257,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_4])).

tff(c_263,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_257])).

tff(c_108,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_98,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_105490,plain,(
    ! [C_2038,A_2039,B_2040] :
      ( v1_funct_1(k2_funct_1(C_2038))
      | k2_relset_1(A_2039,B_2040,C_2038) != B_2040
      | ~ v2_funct_1(C_2038)
      | ~ m1_subset_1(C_2038,k1_zfmisc_1(k2_zfmisc_1(A_2039,B_2040)))
      | ~ v1_funct_2(C_2038,A_2039,B_2040)
      | ~ v1_funct_1(C_2038) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_105499,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_105490])).

tff(c_105508,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_108,c_94,c_98,c_105499])).

tff(c_100,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_202,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_100,c_196])).

tff(c_211,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_202])).

tff(c_104,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_102,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_105496,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_105490])).

tff(c_105505,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_105496])).

tff(c_105509,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_105505])).

tff(c_76,plain,(
    ! [A_49] : k6_relat_1(A_49) = k6_partfun1(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_28,plain,(
    ! [A_16] : v2_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_112,plain,(
    ! [A_16] : v2_funct_1(k6_partfun1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_28])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_312,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_324,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_312])).

tff(c_91244,plain,(
    ! [B_1712,A_1713,C_1714] :
      ( k1_xboole_0 = B_1712
      | k1_relset_1(A_1713,B_1712,C_1714) = A_1713
      | ~ v1_funct_2(C_1714,A_1713,B_1712)
      | ~ m1_subset_1(C_1714,k1_zfmisc_1(k2_zfmisc_1(A_1713,B_1712))) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_91250,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_100,c_91244])).

tff(c_91258,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_324,c_91250])).

tff(c_91259,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_91258])).

tff(c_14,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_116,plain,(
    ! [A_11] : k2_relat_1(k6_partfun1(A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_14])).

tff(c_90,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_110112,plain,(
    ! [B_2146,C_2147,A_2148] :
      ( k6_partfun1(B_2146) = k5_relat_1(k2_funct_1(C_2147),C_2147)
      | k1_xboole_0 = B_2146
      | ~ v2_funct_1(C_2147)
      | k2_relset_1(A_2148,B_2146,C_2147) != B_2146
      | ~ m1_subset_1(C_2147,k1_zfmisc_1(k2_zfmisc_1(A_2148,B_2146)))
      | ~ v1_funct_2(C_2147,A_2148,B_2146)
      | ~ v1_funct_1(C_2147) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_110120,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_110112])).

tff(c_110131,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_108,c_98,c_94,c_110120])).

tff(c_110132,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_110131])).

tff(c_42,plain,(
    ! [A_22] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_22),A_22)) = k2_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_110182,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_110132,c_42])).

tff(c_110203,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_110,c_94,c_116,c_110182])).

tff(c_97958,plain,(
    ! [F_1854,C_1852,B_1856,D_1853,E_1857,A_1855] :
      ( k1_partfun1(A_1855,B_1856,C_1852,D_1853,E_1857,F_1854) = k5_relat_1(E_1857,F_1854)
      | ~ m1_subset_1(F_1854,k1_zfmisc_1(k2_zfmisc_1(C_1852,D_1853)))
      | ~ v1_funct_1(F_1854)
      | ~ m1_subset_1(E_1857,k1_zfmisc_1(k2_zfmisc_1(A_1855,B_1856)))
      | ~ v1_funct_1(E_1857) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_97962,plain,(
    ! [A_1855,B_1856,E_1857] :
      ( k1_partfun1(A_1855,B_1856,'#skF_2','#skF_1',E_1857,'#skF_4') = k5_relat_1(E_1857,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_1857,k1_zfmisc_1(k2_zfmisc_1(A_1855,B_1856)))
      | ~ v1_funct_1(E_1857) ) ),
    inference(resolution,[status(thm)],[c_100,c_97958])).

tff(c_98274,plain,(
    ! [A_1861,B_1862,E_1863] :
      ( k1_partfun1(A_1861,B_1862,'#skF_2','#skF_1',E_1863,'#skF_4') = k5_relat_1(E_1863,'#skF_4')
      | ~ m1_subset_1(E_1863,k1_zfmisc_1(k2_zfmisc_1(A_1861,B_1862)))
      | ~ v1_funct_1(E_1863) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_97962])).

tff(c_98283,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_98274])).

tff(c_98290,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_98283])).

tff(c_72,plain,(
    ! [A_42] : m1_subset_1(k6_partfun1(A_42),k1_zfmisc_1(k2_zfmisc_1(A_42,A_42))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_96,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_93245,plain,(
    ! [D_1734,C_1735,A_1736,B_1737] :
      ( D_1734 = C_1735
      | ~ r2_relset_1(A_1736,B_1737,C_1735,D_1734)
      | ~ m1_subset_1(D_1734,k1_zfmisc_1(k2_zfmisc_1(A_1736,B_1737)))
      | ~ m1_subset_1(C_1735,k1_zfmisc_1(k2_zfmisc_1(A_1736,B_1737))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_93253,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_96,c_93245])).

tff(c_93268,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_93253])).

tff(c_93328,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_93268])).

tff(c_98297,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98290,c_93328])).

tff(c_99196,plain,(
    ! [E_1883,C_1882,D_1880,F_1878,B_1881,A_1879] :
      ( m1_subset_1(k1_partfun1(A_1879,B_1881,C_1882,D_1880,E_1883,F_1878),k1_zfmisc_1(k2_zfmisc_1(A_1879,D_1880)))
      | ~ m1_subset_1(F_1878,k1_zfmisc_1(k2_zfmisc_1(C_1882,D_1880)))
      | ~ v1_funct_1(F_1878)
      | ~ m1_subset_1(E_1883,k1_zfmisc_1(k2_zfmisc_1(A_1879,B_1881)))
      | ~ v1_funct_1(E_1883) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_99257,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_98290,c_99196])).

tff(c_99286,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_106,c_104,c_100,c_99257])).

tff(c_99288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98297,c_99286])).

tff(c_99289,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_93268])).

tff(c_108624,plain,(
    ! [D_2117,B_2120,F_2118,A_2119,E_2121,C_2116] :
      ( k1_partfun1(A_2119,B_2120,C_2116,D_2117,E_2121,F_2118) = k5_relat_1(E_2121,F_2118)
      | ~ m1_subset_1(F_2118,k1_zfmisc_1(k2_zfmisc_1(C_2116,D_2117)))
      | ~ v1_funct_1(F_2118)
      | ~ m1_subset_1(E_2121,k1_zfmisc_1(k2_zfmisc_1(A_2119,B_2120)))
      | ~ v1_funct_1(E_2121) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_108628,plain,(
    ! [A_2119,B_2120,E_2121] :
      ( k1_partfun1(A_2119,B_2120,'#skF_2','#skF_1',E_2121,'#skF_4') = k5_relat_1(E_2121,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_2121,k1_zfmisc_1(k2_zfmisc_1(A_2119,B_2120)))
      | ~ v1_funct_1(E_2121) ) ),
    inference(resolution,[status(thm)],[c_100,c_108624])).

tff(c_110484,plain,(
    ! [A_2158,B_2159,E_2160] :
      ( k1_partfun1(A_2158,B_2159,'#skF_2','#skF_1',E_2160,'#skF_4') = k5_relat_1(E_2160,'#skF_4')
      | ~ m1_subset_1(E_2160,k1_zfmisc_1(k2_zfmisc_1(A_2158,B_2159)))
      | ~ v1_funct_1(E_2160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_108628])).

tff(c_110496,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_110484])).

tff(c_110504,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_99289,c_110496])).

tff(c_30,plain,(
    ! [A_17,B_19] :
      ( v2_funct_1(A_17)
      | k2_relat_1(B_19) != k1_relat_1(A_17)
      | ~ v2_funct_1(k5_relat_1(B_19,A_17))
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_110597,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_110504,c_30])).

tff(c_110607,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_104,c_214,c_110,c_112,c_91259,c_110203,c_110597])).

tff(c_110609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105509,c_110607])).

tff(c_110611,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_105505])).

tff(c_20,plain,(
    ! [A_14] :
      ( k4_relat_1(A_14) = k2_funct_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_110751,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_110611,c_20])).

tff(c_110754,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_104,c_110751])).

tff(c_110820,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_110754,c_4])).

tff(c_110866,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_110820])).

tff(c_22,plain,(
    ! [A_15] :
      ( v1_funct_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_114849,plain,(
    ! [B_2262,C_2263,A_2264] :
      ( k6_partfun1(B_2262) = k5_relat_1(k2_funct_1(C_2263),C_2263)
      | k1_xboole_0 = B_2262
      | ~ v2_funct_1(C_2263)
      | k2_relset_1(A_2264,B_2262,C_2263) != B_2262
      | ~ m1_subset_1(C_2263,k1_zfmisc_1(k2_zfmisc_1(A_2264,B_2262)))
      | ~ v1_funct_2(C_2263,A_2264,B_2262)
      | ~ v1_funct_1(C_2263) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_114857,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_114849])).

tff(c_114868,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_108,c_98,c_94,c_114857])).

tff(c_114869,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_114868])).

tff(c_114984,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_114869,c_42])).

tff(c_115005,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_110,c_94,c_116,c_114984])).

tff(c_36,plain,(
    ! [A_20] :
      ( k1_relat_1(k2_funct_1(A_20)) = k2_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_114644,plain,(
    ! [A_2256,C_2257,B_2258] :
      ( k6_partfun1(A_2256) = k5_relat_1(C_2257,k2_funct_1(C_2257))
      | k1_xboole_0 = B_2258
      | ~ v2_funct_1(C_2257)
      | k2_relset_1(A_2256,B_2258,C_2257) != B_2258
      | ~ m1_subset_1(C_2257,k1_zfmisc_1(k2_zfmisc_1(A_2256,B_2258)))
      | ~ v1_funct_2(C_2257,A_2256,B_2258)
      | ~ v1_funct_1(C_2257) ) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_114652,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_114644])).

tff(c_114663,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_108,c_98,c_94,c_114652])).

tff(c_114664,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_114663])).

tff(c_114700,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_114664,c_30])).

tff(c_114719,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_105508,c_214,c_110,c_112,c_114700])).

tff(c_114839,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_114719])).

tff(c_114842,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_114839])).

tff(c_114846,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_110,c_94,c_114842])).

tff(c_114848,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_114719])).

tff(c_115023,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115005,c_114848])).

tff(c_16,plain,(
    ! [A_12] : k4_relat_1(k6_relat_1(A_12)) = k6_relat_1(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_115,plain,(
    ! [A_12] : k4_relat_1(k6_partfun1(A_12)) = k6_partfun1(A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_76,c_16])).

tff(c_113437,plain,(
    ! [F_2228,A_2229,E_2231,C_2226,D_2227,B_2230] :
      ( k1_partfun1(A_2229,B_2230,C_2226,D_2227,E_2231,F_2228) = k5_relat_1(E_2231,F_2228)
      | ~ m1_subset_1(F_2228,k1_zfmisc_1(k2_zfmisc_1(C_2226,D_2227)))
      | ~ v1_funct_1(F_2228)
      | ~ m1_subset_1(E_2231,k1_zfmisc_1(k2_zfmisc_1(A_2229,B_2230)))
      | ~ v1_funct_1(E_2231) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_113441,plain,(
    ! [A_2229,B_2230,E_2231] :
      ( k1_partfun1(A_2229,B_2230,'#skF_2','#skF_1',E_2231,'#skF_4') = k5_relat_1(E_2231,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_2231,k1_zfmisc_1(k2_zfmisc_1(A_2229,B_2230)))
      | ~ v1_funct_1(E_2231) ) ),
    inference(resolution,[status(thm)],[c_100,c_113437])).

tff(c_114733,plain,(
    ! [A_2259,B_2260,E_2261] :
      ( k1_partfun1(A_2259,B_2260,'#skF_2','#skF_1',E_2261,'#skF_4') = k5_relat_1(E_2261,'#skF_4')
      | ~ m1_subset_1(E_2261,k1_zfmisc_1(k2_zfmisc_1(A_2259,B_2260)))
      | ~ v1_funct_1(E_2261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_113441])).

tff(c_114745,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_114733])).

tff(c_114753,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_99289,c_114745])).

tff(c_353,plain,(
    ! [B_89,A_90] :
      ( k5_relat_1(k4_relat_1(B_89),k4_relat_1(A_90)) = k4_relat_1(k5_relat_1(A_90,B_89))
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_371,plain,(
    ! [B_89] :
      ( k5_relat_1(k4_relat_1(B_89),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3',B_89))
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_353])).

tff(c_393,plain,(
    ! [B_89] :
      ( k5_relat_1(k4_relat_1(B_89),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3',B_89))
      | ~ v1_relat_1(B_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_371])).

tff(c_110805,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_110754,c_393])).

tff(c_110856,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_110805])).

tff(c_114757,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1('#skF_3')) = k4_relat_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114753,c_110856])).

tff(c_114761,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_114757])).

tff(c_32,plain,(
    ! [B_19,A_17] :
      ( v2_funct_1(B_19)
      | k2_relat_1(B_19) != k1_relat_1(A_17)
      | ~ v2_funct_1(k5_relat_1(B_19,A_17))
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_114786,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_114761,c_32])).

tff(c_114800,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_105508,c_110866,c_112,c_114786])).

tff(c_127191,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1(k2_funct_1('#skF_4')) != '#skF_2'
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115023,c_114800])).

tff(c_127192,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_127191])).

tff(c_127195,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_127192])).

tff(c_127199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_104,c_127195])).

tff(c_127201,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_127191])).

tff(c_114847,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_114719])).

tff(c_34,plain,(
    ! [A_20] :
      ( k2_relat_1(k2_funct_1(A_20)) = k1_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_127200,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_2'
    | v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_127191])).

tff(c_127206,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_127200])).

tff(c_127209,plain,
    ( k1_relat_1('#skF_4') != '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_127206])).

tff(c_127212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_104,c_110611,c_91259,c_127209])).

tff(c_127214,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_127200])).

tff(c_325,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_312])).

tff(c_91253,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_106,c_91244])).

tff(c_91262,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_325,c_91253])).

tff(c_91263,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_91262])).

tff(c_8,plain,(
    ! [A_7] :
      ( k4_relat_1(k4_relat_1(A_7)) = A_7
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_254,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_8])).

tff(c_261,plain,(
    k4_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_254])).

tff(c_114872,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_114847,c_20])).

tff(c_114875,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_105508,c_261,c_114872])).

tff(c_46,plain,(
    ! [A_23,B_25] :
      ( k2_funct_1(A_23) = B_25
      | k6_relat_1(k2_relat_1(A_23)) != k5_relat_1(B_25,A_23)
      | k2_relat_1(B_25) != k1_relat_1(A_23)
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_110612,plain,(
    ! [A_2161,B_2162] :
      ( k2_funct_1(A_2161) = B_2162
      | k6_partfun1(k2_relat_1(A_2161)) != k5_relat_1(B_2162,A_2161)
      | k2_relat_1(B_2162) != k1_relat_1(A_2161)
      | ~ v2_funct_1(A_2161)
      | ~ v1_funct_1(B_2162)
      | ~ v1_relat_1(B_2162)
      | ~ v1_funct_1(A_2161)
      | ~ v1_relat_1(A_2161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_46])).

tff(c_135404,plain,(
    ! [A_2478,B_2479] :
      ( k2_funct_1(k2_funct_1(A_2478)) = B_2479
      | k5_relat_1(B_2479,k2_funct_1(A_2478)) != k6_partfun1(k1_relat_1(A_2478))
      | k2_relat_1(B_2479) != k1_relat_1(k2_funct_1(A_2478))
      | ~ v2_funct_1(k2_funct_1(A_2478))
      | ~ v1_funct_1(B_2479)
      | ~ v1_relat_1(B_2479)
      | ~ v1_funct_1(k2_funct_1(A_2478))
      | ~ v1_relat_1(k2_funct_1(A_2478))
      | ~ v2_funct_1(A_2478)
      | ~ v1_funct_1(A_2478)
      | ~ v1_relat_1(A_2478) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_110612])).

tff(c_135420,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = k2_funct_1('#skF_4')
    | k6_partfun1(k1_relat_1('#skF_3')) != k6_partfun1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_114761,c_135404])).

tff(c_135457,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_110,c_94,c_263,c_105508,c_110866,c_127201,c_114847,c_115023,c_127214,c_91263,c_114875,c_135420])).

tff(c_110817,plain,
    ( k4_relat_1(k2_funct_1('#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_110754,c_8])).

tff(c_110864,plain,(
    k4_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_110817])).

tff(c_127213,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_127200])).

tff(c_127217,plain,
    ( k4_relat_1(k2_funct_1('#skF_4')) = k2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_127213,c_20])).

tff(c_127220,plain,(
    k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110866,c_127201,c_110864,c_127217])).

tff(c_135499,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135457,c_127220])).

tff(c_135531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_135499])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 34.14/24.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.14/24.27  
% 34.14/24.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.14/24.28  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 34.14/24.28  
% 34.14/24.28  %Foreground sorts:
% 34.14/24.28  
% 34.14/24.28  
% 34.14/24.28  %Background operators:
% 34.14/24.28  
% 34.14/24.28  
% 34.14/24.28  %Foreground operators:
% 34.14/24.28  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 34.14/24.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 34.14/24.28  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 34.14/24.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 34.14/24.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 34.14/24.28  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 34.14/24.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 34.14/24.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 34.14/24.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 34.14/24.28  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 34.14/24.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 34.14/24.28  tff('#skF_2', type, '#skF_2': $i).
% 34.14/24.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 34.14/24.28  tff('#skF_3', type, '#skF_3': $i).
% 34.14/24.28  tff('#skF_1', type, '#skF_1': $i).
% 34.14/24.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 34.14/24.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 34.14/24.28  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 34.14/24.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 34.14/24.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 34.14/24.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 34.14/24.28  tff('#skF_4', type, '#skF_4': $i).
% 34.14/24.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 34.14/24.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 34.14/24.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 34.14/24.28  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 34.14/24.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 34.14/24.28  
% 34.39/24.30  tff(f_259, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 34.39/24.30  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 34.39/24.30  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 34.39/24.30  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 34.39/24.30  tff(f_36, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 34.39/24.30  tff(f_217, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 34.39/24.30  tff(f_201, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 34.39/24.30  tff(f_79, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 34.39/24.30  tff(f_147, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 34.39/24.30  tff(f_173, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 34.39/24.30  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 34.39/24.30  tff(f_233, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 34.39/24.30  tff(f_126, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 34.39/24.30  tff(f_199, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 34.39/24.30  tff(f_189, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 34.39/24.30  tff(f_155, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 34.39/24.30  tff(f_185, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 34.39/24.30  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 34.39/24.30  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 34.39/24.30  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 34.39/24.30  tff(f_55, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 34.39/24.30  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 34.39/24.30  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 34.39/24.30  tff(f_143, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 34.39/24.30  tff(c_88, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_259])).
% 34.39/24.30  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 34.39/24.30  tff(c_106, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_259])).
% 34.39/24.30  tff(c_196, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_32])).
% 34.39/24.30  tff(c_205, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_106, c_196])).
% 34.39/24.30  tff(c_214, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_205])).
% 34.39/24.30  tff(c_110, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_259])).
% 34.39/24.30  tff(c_94, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_259])).
% 34.39/24.30  tff(c_238, plain, (![A_75]: (k4_relat_1(A_75)=k2_funct_1(A_75) | ~v2_funct_1(A_75) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_67])).
% 34.39/24.30  tff(c_244, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_238])).
% 34.39/24.30  tff(c_250, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_214, c_110, c_244])).
% 34.39/24.30  tff(c_4, plain, (![A_4]: (v1_relat_1(k4_relat_1(A_4)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 34.39/24.30  tff(c_257, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_250, c_4])).
% 34.39/24.30  tff(c_263, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_257])).
% 34.39/24.30  tff(c_108, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_259])).
% 34.39/24.30  tff(c_98, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_259])).
% 34.39/24.30  tff(c_105490, plain, (![C_2038, A_2039, B_2040]: (v1_funct_1(k2_funct_1(C_2038)) | k2_relset_1(A_2039, B_2040, C_2038)!=B_2040 | ~v2_funct_1(C_2038) | ~m1_subset_1(C_2038, k1_zfmisc_1(k2_zfmisc_1(A_2039, B_2040))) | ~v1_funct_2(C_2038, A_2039, B_2040) | ~v1_funct_1(C_2038))), inference(cnfTransformation, [status(thm)], [f_217])).
% 34.39/24.30  tff(c_105499, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_105490])).
% 34.39/24.30  tff(c_105508, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_108, c_94, c_98, c_105499])).
% 34.39/24.30  tff(c_100, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_259])).
% 34.39/24.30  tff(c_202, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_100, c_196])).
% 34.39/24.30  tff(c_211, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_202])).
% 34.39/24.30  tff(c_104, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_259])).
% 34.39/24.30  tff(c_102, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_259])).
% 34.39/24.30  tff(c_105496, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_105490])).
% 34.39/24.30  tff(c_105505, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_105496])).
% 34.39/24.30  tff(c_105509, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_105505])).
% 34.39/24.30  tff(c_76, plain, (![A_49]: (k6_relat_1(A_49)=k6_partfun1(A_49))), inference(cnfTransformation, [status(thm)], [f_201])).
% 34.39/24.30  tff(c_28, plain, (![A_16]: (v2_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 34.39/24.30  tff(c_112, plain, (![A_16]: (v2_funct_1(k6_partfun1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_28])).
% 34.39/24.30  tff(c_92, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_259])).
% 34.39/24.30  tff(c_312, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 34.39/24.30  tff(c_324, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_312])).
% 34.39/24.30  tff(c_91244, plain, (![B_1712, A_1713, C_1714]: (k1_xboole_0=B_1712 | k1_relset_1(A_1713, B_1712, C_1714)=A_1713 | ~v1_funct_2(C_1714, A_1713, B_1712) | ~m1_subset_1(C_1714, k1_zfmisc_1(k2_zfmisc_1(A_1713, B_1712))))), inference(cnfTransformation, [status(thm)], [f_173])).
% 34.39/24.30  tff(c_91250, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_100, c_91244])).
% 34.39/24.30  tff(c_91258, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_324, c_91250])).
% 34.39/24.30  tff(c_91259, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_92, c_91258])).
% 34.39/24.30  tff(c_14, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_53])).
% 34.39/24.30  tff(c_116, plain, (![A_11]: (k2_relat_1(k6_partfun1(A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_14])).
% 34.39/24.30  tff(c_90, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_259])).
% 34.39/24.30  tff(c_110112, plain, (![B_2146, C_2147, A_2148]: (k6_partfun1(B_2146)=k5_relat_1(k2_funct_1(C_2147), C_2147) | k1_xboole_0=B_2146 | ~v2_funct_1(C_2147) | k2_relset_1(A_2148, B_2146, C_2147)!=B_2146 | ~m1_subset_1(C_2147, k1_zfmisc_1(k2_zfmisc_1(A_2148, B_2146))) | ~v1_funct_2(C_2147, A_2148, B_2146) | ~v1_funct_1(C_2147))), inference(cnfTransformation, [status(thm)], [f_233])).
% 34.39/24.30  tff(c_110120, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_110112])).
% 34.39/24.30  tff(c_110131, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_108, c_98, c_94, c_110120])).
% 34.39/24.30  tff(c_110132, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_90, c_110131])).
% 34.39/24.30  tff(c_42, plain, (![A_22]: (k2_relat_1(k5_relat_1(k2_funct_1(A_22), A_22))=k2_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_126])).
% 34.39/24.30  tff(c_110182, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_110132, c_42])).
% 34.39/24.30  tff(c_110203, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_214, c_110, c_94, c_116, c_110182])).
% 34.39/24.30  tff(c_97958, plain, (![F_1854, C_1852, B_1856, D_1853, E_1857, A_1855]: (k1_partfun1(A_1855, B_1856, C_1852, D_1853, E_1857, F_1854)=k5_relat_1(E_1857, F_1854) | ~m1_subset_1(F_1854, k1_zfmisc_1(k2_zfmisc_1(C_1852, D_1853))) | ~v1_funct_1(F_1854) | ~m1_subset_1(E_1857, k1_zfmisc_1(k2_zfmisc_1(A_1855, B_1856))) | ~v1_funct_1(E_1857))), inference(cnfTransformation, [status(thm)], [f_199])).
% 34.39/24.30  tff(c_97962, plain, (![A_1855, B_1856, E_1857]: (k1_partfun1(A_1855, B_1856, '#skF_2', '#skF_1', E_1857, '#skF_4')=k5_relat_1(E_1857, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_1857, k1_zfmisc_1(k2_zfmisc_1(A_1855, B_1856))) | ~v1_funct_1(E_1857))), inference(resolution, [status(thm)], [c_100, c_97958])).
% 34.39/24.30  tff(c_98274, plain, (![A_1861, B_1862, E_1863]: (k1_partfun1(A_1861, B_1862, '#skF_2', '#skF_1', E_1863, '#skF_4')=k5_relat_1(E_1863, '#skF_4') | ~m1_subset_1(E_1863, k1_zfmisc_1(k2_zfmisc_1(A_1861, B_1862))) | ~v1_funct_1(E_1863))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_97962])).
% 34.39/24.30  tff(c_98283, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_98274])).
% 34.39/24.30  tff(c_98290, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_98283])).
% 34.39/24.30  tff(c_72, plain, (![A_42]: (m1_subset_1(k6_partfun1(A_42), k1_zfmisc_1(k2_zfmisc_1(A_42, A_42))))), inference(cnfTransformation, [status(thm)], [f_189])).
% 34.39/24.30  tff(c_96, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_259])).
% 34.39/24.30  tff(c_93245, plain, (![D_1734, C_1735, A_1736, B_1737]: (D_1734=C_1735 | ~r2_relset_1(A_1736, B_1737, C_1735, D_1734) | ~m1_subset_1(D_1734, k1_zfmisc_1(k2_zfmisc_1(A_1736, B_1737))) | ~m1_subset_1(C_1735, k1_zfmisc_1(k2_zfmisc_1(A_1736, B_1737))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 34.39/24.30  tff(c_93253, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_96, c_93245])).
% 34.39/24.30  tff(c_93268, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_93253])).
% 34.39/24.30  tff(c_93328, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_93268])).
% 34.39/24.30  tff(c_98297, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_98290, c_93328])).
% 34.39/24.30  tff(c_99196, plain, (![E_1883, C_1882, D_1880, F_1878, B_1881, A_1879]: (m1_subset_1(k1_partfun1(A_1879, B_1881, C_1882, D_1880, E_1883, F_1878), k1_zfmisc_1(k2_zfmisc_1(A_1879, D_1880))) | ~m1_subset_1(F_1878, k1_zfmisc_1(k2_zfmisc_1(C_1882, D_1880))) | ~v1_funct_1(F_1878) | ~m1_subset_1(E_1883, k1_zfmisc_1(k2_zfmisc_1(A_1879, B_1881))) | ~v1_funct_1(E_1883))), inference(cnfTransformation, [status(thm)], [f_185])).
% 34.39/24.30  tff(c_99257, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_98290, c_99196])).
% 34.39/24.30  tff(c_99286, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_106, c_104, c_100, c_99257])).
% 34.39/24.30  tff(c_99288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98297, c_99286])).
% 34.39/24.30  tff(c_99289, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_93268])).
% 34.39/24.30  tff(c_108624, plain, (![D_2117, B_2120, F_2118, A_2119, E_2121, C_2116]: (k1_partfun1(A_2119, B_2120, C_2116, D_2117, E_2121, F_2118)=k5_relat_1(E_2121, F_2118) | ~m1_subset_1(F_2118, k1_zfmisc_1(k2_zfmisc_1(C_2116, D_2117))) | ~v1_funct_1(F_2118) | ~m1_subset_1(E_2121, k1_zfmisc_1(k2_zfmisc_1(A_2119, B_2120))) | ~v1_funct_1(E_2121))), inference(cnfTransformation, [status(thm)], [f_199])).
% 34.39/24.30  tff(c_108628, plain, (![A_2119, B_2120, E_2121]: (k1_partfun1(A_2119, B_2120, '#skF_2', '#skF_1', E_2121, '#skF_4')=k5_relat_1(E_2121, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_2121, k1_zfmisc_1(k2_zfmisc_1(A_2119, B_2120))) | ~v1_funct_1(E_2121))), inference(resolution, [status(thm)], [c_100, c_108624])).
% 34.39/24.30  tff(c_110484, plain, (![A_2158, B_2159, E_2160]: (k1_partfun1(A_2158, B_2159, '#skF_2', '#skF_1', E_2160, '#skF_4')=k5_relat_1(E_2160, '#skF_4') | ~m1_subset_1(E_2160, k1_zfmisc_1(k2_zfmisc_1(A_2158, B_2159))) | ~v1_funct_1(E_2160))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_108628])).
% 34.39/24.30  tff(c_110496, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_110484])).
% 34.39/24.30  tff(c_110504, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_99289, c_110496])).
% 34.39/24.30  tff(c_30, plain, (![A_17, B_19]: (v2_funct_1(A_17) | k2_relat_1(B_19)!=k1_relat_1(A_17) | ~v2_funct_1(k5_relat_1(B_19, A_17)) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_96])).
% 34.39/24.30  tff(c_110597, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_110504, c_30])).
% 34.39/24.30  tff(c_110607, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_104, c_214, c_110, c_112, c_91259, c_110203, c_110597])).
% 34.39/24.30  tff(c_110609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105509, c_110607])).
% 34.39/24.30  tff(c_110611, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_105505])).
% 34.39/24.30  tff(c_20, plain, (![A_14]: (k4_relat_1(A_14)=k2_funct_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 34.39/24.30  tff(c_110751, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_110611, c_20])).
% 34.39/24.30  tff(c_110754, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_104, c_110751])).
% 34.39/24.30  tff(c_110820, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_110754, c_4])).
% 34.39/24.30  tff(c_110866, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_110820])).
% 34.39/24.30  tff(c_22, plain, (![A_15]: (v1_funct_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_75])).
% 34.39/24.30  tff(c_114849, plain, (![B_2262, C_2263, A_2264]: (k6_partfun1(B_2262)=k5_relat_1(k2_funct_1(C_2263), C_2263) | k1_xboole_0=B_2262 | ~v2_funct_1(C_2263) | k2_relset_1(A_2264, B_2262, C_2263)!=B_2262 | ~m1_subset_1(C_2263, k1_zfmisc_1(k2_zfmisc_1(A_2264, B_2262))) | ~v1_funct_2(C_2263, A_2264, B_2262) | ~v1_funct_1(C_2263))), inference(cnfTransformation, [status(thm)], [f_233])).
% 34.39/24.30  tff(c_114857, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_114849])).
% 34.39/24.30  tff(c_114868, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_108, c_98, c_94, c_114857])).
% 34.39/24.30  tff(c_114869, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_90, c_114868])).
% 34.39/24.30  tff(c_114984, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_114869, c_42])).
% 34.39/24.30  tff(c_115005, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_214, c_110, c_94, c_116, c_114984])).
% 34.39/24.30  tff(c_36, plain, (![A_20]: (k1_relat_1(k2_funct_1(A_20))=k2_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_106])).
% 34.39/24.30  tff(c_114644, plain, (![A_2256, C_2257, B_2258]: (k6_partfun1(A_2256)=k5_relat_1(C_2257, k2_funct_1(C_2257)) | k1_xboole_0=B_2258 | ~v2_funct_1(C_2257) | k2_relset_1(A_2256, B_2258, C_2257)!=B_2258 | ~m1_subset_1(C_2257, k1_zfmisc_1(k2_zfmisc_1(A_2256, B_2258))) | ~v1_funct_2(C_2257, A_2256, B_2258) | ~v1_funct_1(C_2257))), inference(cnfTransformation, [status(thm)], [f_233])).
% 34.39/24.30  tff(c_114652, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_114644])).
% 34.39/24.30  tff(c_114663, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_108, c_98, c_94, c_114652])).
% 34.39/24.30  tff(c_114664, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_90, c_114663])).
% 34.39/24.30  tff(c_114700, plain, (v2_funct_1(k2_funct_1('#skF_3')) | k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_114664, c_30])).
% 34.39/24.30  tff(c_114719, plain, (v2_funct_1(k2_funct_1('#skF_3')) | k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_105508, c_214, c_110, c_112, c_114700])).
% 34.39/24.31  tff(c_114839, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_114719])).
% 34.39/24.31  tff(c_114842, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_114839])).
% 34.39/24.31  tff(c_114846, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_110, c_94, c_114842])).
% 34.39/24.31  tff(c_114848, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_114719])).
% 34.39/24.31  tff(c_115023, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_115005, c_114848])).
% 34.39/24.31  tff(c_16, plain, (![A_12]: (k4_relat_1(k6_relat_1(A_12))=k6_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 34.39/24.31  tff(c_115, plain, (![A_12]: (k4_relat_1(k6_partfun1(A_12))=k6_partfun1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_76, c_16])).
% 34.39/24.31  tff(c_113437, plain, (![F_2228, A_2229, E_2231, C_2226, D_2227, B_2230]: (k1_partfun1(A_2229, B_2230, C_2226, D_2227, E_2231, F_2228)=k5_relat_1(E_2231, F_2228) | ~m1_subset_1(F_2228, k1_zfmisc_1(k2_zfmisc_1(C_2226, D_2227))) | ~v1_funct_1(F_2228) | ~m1_subset_1(E_2231, k1_zfmisc_1(k2_zfmisc_1(A_2229, B_2230))) | ~v1_funct_1(E_2231))), inference(cnfTransformation, [status(thm)], [f_199])).
% 34.39/24.31  tff(c_113441, plain, (![A_2229, B_2230, E_2231]: (k1_partfun1(A_2229, B_2230, '#skF_2', '#skF_1', E_2231, '#skF_4')=k5_relat_1(E_2231, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_2231, k1_zfmisc_1(k2_zfmisc_1(A_2229, B_2230))) | ~v1_funct_1(E_2231))), inference(resolution, [status(thm)], [c_100, c_113437])).
% 34.39/24.31  tff(c_114733, plain, (![A_2259, B_2260, E_2261]: (k1_partfun1(A_2259, B_2260, '#skF_2', '#skF_1', E_2261, '#skF_4')=k5_relat_1(E_2261, '#skF_4') | ~m1_subset_1(E_2261, k1_zfmisc_1(k2_zfmisc_1(A_2259, B_2260))) | ~v1_funct_1(E_2261))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_113441])).
% 34.39/24.31  tff(c_114745, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_114733])).
% 34.39/24.31  tff(c_114753, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_99289, c_114745])).
% 34.39/24.31  tff(c_353, plain, (![B_89, A_90]: (k5_relat_1(k4_relat_1(B_89), k4_relat_1(A_90))=k4_relat_1(k5_relat_1(A_90, B_89)) | ~v1_relat_1(B_89) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_49])).
% 34.39/24.31  tff(c_371, plain, (![B_89]: (k5_relat_1(k4_relat_1(B_89), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', B_89)) | ~v1_relat_1(B_89) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_250, c_353])).
% 34.39/24.31  tff(c_393, plain, (![B_89]: (k5_relat_1(k4_relat_1(B_89), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', B_89)) | ~v1_relat_1(B_89))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_371])).
% 34.39/24.31  tff(c_110805, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_110754, c_393])).
% 34.39/24.31  tff(c_110856, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_110805])).
% 34.39/24.31  tff(c_114757, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1('#skF_3'))=k4_relat_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_114753, c_110856])).
% 34.39/24.31  tff(c_114761, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_114757])).
% 34.39/24.31  tff(c_32, plain, (![B_19, A_17]: (v2_funct_1(B_19) | k2_relat_1(B_19)!=k1_relat_1(A_17) | ~v2_funct_1(k5_relat_1(B_19, A_17)) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_96])).
% 34.39/24.31  tff(c_114786, plain, (v2_funct_1(k2_funct_1('#skF_4')) | k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_114761, c_32])).
% 34.39/24.31  tff(c_114800, plain, (v2_funct_1(k2_funct_1('#skF_4')) | k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_105508, c_110866, c_112, c_114786])).
% 34.39/24.31  tff(c_127191, plain, (v2_funct_1(k2_funct_1('#skF_4')) | k2_relat_1(k2_funct_1('#skF_4'))!='#skF_2' | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_115023, c_114800])).
% 34.39/24.31  tff(c_127192, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_127191])).
% 34.39/24.31  tff(c_127195, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_127192])).
% 34.39/24.31  tff(c_127199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_211, c_104, c_127195])).
% 34.39/24.31  tff(c_127201, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_127191])).
% 34.39/24.31  tff(c_114847, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_114719])).
% 34.39/24.31  tff(c_34, plain, (![A_20]: (k2_relat_1(k2_funct_1(A_20))=k1_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_106])).
% 34.39/24.31  tff(c_127200, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_2' | v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_127191])).
% 34.39/24.31  tff(c_127206, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_127200])).
% 34.39/24.31  tff(c_127209, plain, (k1_relat_1('#skF_4')!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34, c_127206])).
% 34.39/24.31  tff(c_127212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_211, c_104, c_110611, c_91259, c_127209])).
% 34.39/24.31  tff(c_127214, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_127200])).
% 34.39/24.31  tff(c_325, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_312])).
% 34.39/24.31  tff(c_91253, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_106, c_91244])).
% 34.39/24.31  tff(c_91262, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_325, c_91253])).
% 34.39/24.31  tff(c_91263, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_90, c_91262])).
% 34.39/24.31  tff(c_8, plain, (![A_7]: (k4_relat_1(k4_relat_1(A_7))=A_7 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 34.39/24.31  tff(c_254, plain, (k4_relat_1(k2_funct_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_250, c_8])).
% 34.39/24.31  tff(c_261, plain, (k4_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_214, c_254])).
% 34.39/24.31  tff(c_114872, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_114847, c_20])).
% 34.39/24.31  tff(c_114875, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_263, c_105508, c_261, c_114872])).
% 34.39/24.31  tff(c_46, plain, (![A_23, B_25]: (k2_funct_1(A_23)=B_25 | k6_relat_1(k2_relat_1(A_23))!=k5_relat_1(B_25, A_23) | k2_relat_1(B_25)!=k1_relat_1(A_23) | ~v2_funct_1(A_23) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_143])).
% 34.39/24.31  tff(c_110612, plain, (![A_2161, B_2162]: (k2_funct_1(A_2161)=B_2162 | k6_partfun1(k2_relat_1(A_2161))!=k5_relat_1(B_2162, A_2161) | k2_relat_1(B_2162)!=k1_relat_1(A_2161) | ~v2_funct_1(A_2161) | ~v1_funct_1(B_2162) | ~v1_relat_1(B_2162) | ~v1_funct_1(A_2161) | ~v1_relat_1(A_2161))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_46])).
% 34.39/24.31  tff(c_135404, plain, (![A_2478, B_2479]: (k2_funct_1(k2_funct_1(A_2478))=B_2479 | k5_relat_1(B_2479, k2_funct_1(A_2478))!=k6_partfun1(k1_relat_1(A_2478)) | k2_relat_1(B_2479)!=k1_relat_1(k2_funct_1(A_2478)) | ~v2_funct_1(k2_funct_1(A_2478)) | ~v1_funct_1(B_2479) | ~v1_relat_1(B_2479) | ~v1_funct_1(k2_funct_1(A_2478)) | ~v1_relat_1(k2_funct_1(A_2478)) | ~v2_funct_1(A_2478) | ~v1_funct_1(A_2478) | ~v1_relat_1(A_2478))), inference(superposition, [status(thm), theory('equality')], [c_34, c_110612])).
% 34.39/24.31  tff(c_135420, plain, (k2_funct_1(k2_funct_1('#skF_3'))=k2_funct_1('#skF_4') | k6_partfun1(k1_relat_1('#skF_3'))!=k6_partfun1('#skF_1') | k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_114761, c_135404])).
% 34.39/24.31  tff(c_135457, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_214, c_110, c_94, c_263, c_105508, c_110866, c_127201, c_114847, c_115023, c_127214, c_91263, c_114875, c_135420])).
% 34.39/24.31  tff(c_110817, plain, (k4_relat_1(k2_funct_1('#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_110754, c_8])).
% 34.39/24.31  tff(c_110864, plain, (k4_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_110817])).
% 34.39/24.31  tff(c_127213, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_127200])).
% 34.39/24.31  tff(c_127217, plain, (k4_relat_1(k2_funct_1('#skF_4'))=k2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_127213, c_20])).
% 34.39/24.31  tff(c_127220, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_110866, c_127201, c_110864, c_127217])).
% 34.39/24.31  tff(c_135499, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_135457, c_127220])).
% 34.39/24.31  tff(c_135531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_135499])).
% 34.39/24.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.39/24.31  
% 34.39/24.31  Inference rules
% 34.39/24.31  ----------------------
% 34.39/24.31  #Ref     : 0
% 34.39/24.31  #Sup     : 32383
% 34.39/24.31  #Fact    : 0
% 34.39/24.31  #Define  : 0
% 34.39/24.31  #Split   : 271
% 34.39/24.31  #Chain   : 0
% 34.39/24.31  #Close   : 0
% 34.39/24.31  
% 34.39/24.31  Ordering : KBO
% 34.39/24.31  
% 34.39/24.31  Simplification rules
% 34.39/24.31  ----------------------
% 34.39/24.31  #Subsume      : 3950
% 34.39/24.31  #Demod        : 57471
% 34.39/24.31  #Tautology    : 10999
% 34.39/24.31  #SimpNegUnit  : 754
% 34.39/24.31  #BackRed      : 1014
% 34.39/24.31  
% 34.39/24.31  #Partial instantiations: 0
% 34.39/24.31  #Strategies tried      : 1
% 34.39/24.31  
% 34.39/24.31  Timing (in seconds)
% 34.39/24.31  ----------------------
% 34.44/24.31  Preprocessing        : 0.39
% 34.44/24.31  Parsing              : 0.20
% 34.44/24.31  CNF conversion       : 0.03
% 34.44/24.31  Main loop            : 23.12
% 34.44/24.31  Inferencing          : 3.95
% 34.44/24.31  Reduction            : 12.54
% 34.44/24.31  Demodulation         : 10.69
% 34.44/24.31  BG Simplification    : 0.49
% 34.44/24.31  Subsumption          : 5.14
% 34.44/24.31  Abstraction          : 0.83
% 34.44/24.31  MUC search           : 0.00
% 34.44/24.31  Cooper               : 0.00
% 34.44/24.31  Total                : 23.58
% 34.44/24.31  Index Insertion      : 0.00
% 34.44/24.31  Index Deletion       : 0.00
% 34.44/24.31  Index Matching       : 0.00
% 34.44/24.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
