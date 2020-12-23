%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:15 EST 2020

% Result     : Theorem 5.81s
% Output     : CNFRefutation 6.08s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 690 expanded)
%              Number of leaves         :   49 ( 262 expanded)
%              Depth                    :   14
%              Number of atoms          :  395 (2708 expanded)
%              Number of equality atoms :  118 ( 817 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_227,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
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

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_138,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_154,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_164,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_150,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_185,axiom,(
    ! [A,B,C] :
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_166,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_86,axiom,(
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

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_201,axiom,(
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

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
          & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_72,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_84,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_136,plain,(
    ! [B_63,A_64] :
      ( v1_relat_1(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_142,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_84,c_136])).

tff(c_151,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_142])).

tff(c_88,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_86,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_2371,plain,(
    ! [A_357,B_358,C_359] :
      ( k1_relset_1(A_357,B_358,C_359) = k1_relat_1(C_359)
      | ~ m1_subset_1(C_359,k1_zfmisc_1(k2_zfmisc_1(A_357,B_358))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2383,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_2371])).

tff(c_2452,plain,(
    ! [B_370,A_371,C_372] :
      ( k1_xboole_0 = B_370
      | k1_relset_1(A_371,B_370,C_372) = A_371
      | ~ v1_funct_2(C_372,A_371,B_370)
      | ~ m1_subset_1(C_372,k1_zfmisc_1(k2_zfmisc_1(A_371,B_370))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2458,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_2452])).

tff(c_2466,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2383,c_2458])).

tff(c_2467,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2466])).

tff(c_168,plain,(
    ! [C_68,B_69,A_70] :
      ( v5_relat_1(C_68,B_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_179,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_168])).

tff(c_209,plain,(
    ! [B_76,A_77] :
      ( k2_relat_1(B_76) = A_77
      | ~ v2_funct_2(B_76,A_77)
      | ~ v5_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_218,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_179,c_209])).

tff(c_227,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_218])).

tff(c_238,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_94,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_92,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_90,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_58,plain,(
    ! [A_37] : m1_subset_1(k6_partfun1(A_37),k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_228,plain,(
    ! [A_78,B_79,D_80] :
      ( r2_relset_1(A_78,B_79,D_80,D_80)
      | ~ m1_subset_1(D_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_235,plain,(
    ! [A_37] : r2_relset_1(A_37,A_37,k6_partfun1(A_37),k6_partfun1(A_37)) ),
    inference(resolution,[status(thm)],[c_58,c_228])).

tff(c_877,plain,(
    ! [C_200,F_199,E_198,D_201,B_197,A_196] :
      ( k1_partfun1(A_196,B_197,C_200,D_201,E_198,F_199) = k5_relat_1(E_198,F_199)
      | ~ m1_subset_1(F_199,k1_zfmisc_1(k2_zfmisc_1(C_200,D_201)))
      | ~ v1_funct_1(F_199)
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ v1_funct_1(E_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_881,plain,(
    ! [A_196,B_197,E_198] :
      ( k1_partfun1(A_196,B_197,'#skF_2','#skF_1',E_198,'#skF_4') = k5_relat_1(E_198,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ v1_funct_1(E_198) ) ),
    inference(resolution,[status(thm)],[c_84,c_877])).

tff(c_955,plain,(
    ! [A_213,B_214,E_215] :
      ( k1_partfun1(A_213,B_214,'#skF_2','#skF_1',E_215,'#skF_4') = k5_relat_1(E_215,'#skF_4')
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214)))
      | ~ v1_funct_1(E_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_881])).

tff(c_964,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_955])).

tff(c_971,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_964])).

tff(c_80,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_747,plain,(
    ! [D_166,C_167,A_168,B_169] :
      ( D_166 = C_167
      | ~ r2_relset_1(A_168,B_169,C_167,D_166)
      | ~ m1_subset_1(D_166,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_755,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_80,c_747])).

tff(c_770,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_755])).

tff(c_771,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_770])).

tff(c_978,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_971,c_771])).

tff(c_1040,plain,(
    ! [F_228,B_225,C_229,D_224,A_227,E_226] :
      ( m1_subset_1(k1_partfun1(A_227,B_225,C_229,D_224,E_226,F_228),k1_zfmisc_1(k2_zfmisc_1(A_227,D_224)))
      | ~ m1_subset_1(F_228,k1_zfmisc_1(k2_zfmisc_1(C_229,D_224)))
      | ~ v1_funct_1(F_228)
      | ~ m1_subset_1(E_226,k1_zfmisc_1(k2_zfmisc_1(A_227,B_225)))
      | ~ v1_funct_1(E_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1097,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_971,c_1040])).

tff(c_1129,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_88,c_84,c_1097])).

tff(c_1131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_978,c_1129])).

tff(c_1132,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_770])).

tff(c_1931,plain,(
    ! [D_286,A_287,B_288,C_289] :
      ( v2_funct_2(D_286,A_287)
      | ~ r2_relset_1(A_287,A_287,k1_partfun1(A_287,B_288,B_288,A_287,C_289,D_286),k6_partfun1(A_287))
      | ~ m1_subset_1(D_286,k1_zfmisc_1(k2_zfmisc_1(B_288,A_287)))
      | ~ v1_funct_2(D_286,B_288,A_287)
      | ~ v1_funct_1(D_286)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288)))
      | ~ v1_funct_2(C_289,A_287,B_288)
      | ~ v1_funct_1(C_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_1937,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1132,c_1931])).

tff(c_1941,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_90,c_88,c_86,c_84,c_235,c_1937])).

tff(c_1943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_1941])).

tff(c_1944,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_62,plain,(
    ! [A_44] : k6_relat_1(A_44) = k6_partfun1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_22,plain,(
    ! [A_12,B_14] :
      ( k2_funct_1(A_12) = B_14
      | k6_relat_1(k2_relat_1(A_12)) != k5_relat_1(B_14,A_12)
      | k2_relat_1(B_14) != k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2955,plain,(
    ! [A_449,B_450] :
      ( k2_funct_1(A_449) = B_450
      | k6_partfun1(k2_relat_1(A_449)) != k5_relat_1(B_450,A_449)
      | k2_relat_1(B_450) != k1_relat_1(A_449)
      | ~ v2_funct_1(A_449)
      | ~ v1_funct_1(B_450)
      | ~ v1_relat_1(B_450)
      | ~ v1_funct_1(A_449)
      | ~ v1_relat_1(A_449) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_22])).

tff(c_2961,plain,(
    ! [B_450] :
      ( k2_funct_1('#skF_4') = B_450
      | k5_relat_1(B_450,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_450) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_450)
      | ~ v1_relat_1(B_450)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1944,c_2955])).

tff(c_2967,plain,(
    ! [B_450] :
      ( k2_funct_1('#skF_4') = B_450
      | k5_relat_1(B_450,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_450) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_450)
      | ~ v1_relat_1(B_450) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_88,c_2467,c_2961])).

tff(c_2996,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2967])).

tff(c_145,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_90,c_136])).

tff(c_154,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_145])).

tff(c_12,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_96,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_12])).

tff(c_180,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_168])).

tff(c_215,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_180,c_209])).

tff(c_224,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_215])).

tff(c_1956,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_78,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_6,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_99,plain,(
    ! [A_6] : k1_relat_1(k6_partfun1(A_6)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_6])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_82,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_2298,plain,(
    ! [B_353,C_354,A_355] :
      ( k6_partfun1(B_353) = k5_relat_1(k2_funct_1(C_354),C_354)
      | k1_xboole_0 = B_353
      | ~ v2_funct_1(C_354)
      | k2_relset_1(A_355,B_353,C_354) != B_353
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(A_355,B_353)))
      | ~ v1_funct_2(C_354,A_355,B_353)
      | ~ v1_funct_1(C_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_2304,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_2298])).

tff(c_2314,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_78,c_2304])).

tff(c_2315,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2314])).

tff(c_20,plain,(
    ! [A_11] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_11),A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2327,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2315,c_20])).

tff(c_2340,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_94,c_78,c_99,c_2327])).

tff(c_48,plain,(
    ! [B_30] :
      ( v2_funct_2(B_30,k2_relat_1(B_30))
      | ~ v5_relat_1(B_30,k2_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2349,plain,
    ( v2_funct_2('#skF_3',k2_relat_1('#skF_3'))
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2340,c_48])).

tff(c_2355,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_180,c_2340,c_2349])).

tff(c_2357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1956,c_2355])).

tff(c_2358,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_2646,plain,(
    ! [D_416,E_413,F_414,A_411,C_415,B_412] :
      ( k1_partfun1(A_411,B_412,C_415,D_416,E_413,F_414) = k5_relat_1(E_413,F_414)
      | ~ m1_subset_1(F_414,k1_zfmisc_1(k2_zfmisc_1(C_415,D_416)))
      | ~ v1_funct_1(F_414)
      | ~ m1_subset_1(E_413,k1_zfmisc_1(k2_zfmisc_1(A_411,B_412)))
      | ~ v1_funct_1(E_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_2650,plain,(
    ! [A_411,B_412,E_413] :
      ( k1_partfun1(A_411,B_412,'#skF_2','#skF_1',E_413,'#skF_4') = k5_relat_1(E_413,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_413,k1_zfmisc_1(k2_zfmisc_1(A_411,B_412)))
      | ~ v1_funct_1(E_413) ) ),
    inference(resolution,[status(thm)],[c_84,c_2646])).

tff(c_2724,plain,(
    ! [A_428,B_429,E_430] :
      ( k1_partfun1(A_428,B_429,'#skF_2','#skF_1',E_430,'#skF_4') = k5_relat_1(E_430,'#skF_4')
      | ~ m1_subset_1(E_430,k1_zfmisc_1(k2_zfmisc_1(A_428,B_429)))
      | ~ v1_funct_1(E_430) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2650])).

tff(c_2733,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_2724])).

tff(c_2740,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2733])).

tff(c_2512,plain,(
    ! [D_381,C_382,A_383,B_384] :
      ( D_381 = C_382
      | ~ r2_relset_1(A_383,B_384,C_382,D_381)
      | ~ m1_subset_1(D_381,k1_zfmisc_1(k2_zfmisc_1(A_383,B_384)))
      | ~ m1_subset_1(C_382,k1_zfmisc_1(k2_zfmisc_1(A_383,B_384))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2520,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_80,c_2512])).

tff(c_2535,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2520])).

tff(c_2536,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2535])).

tff(c_2747,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2740,c_2536])).

tff(c_2854,plain,(
    ! [C_448,D_443,F_447,B_444,E_445,A_446] :
      ( m1_subset_1(k1_partfun1(A_446,B_444,C_448,D_443,E_445,F_447),k1_zfmisc_1(k2_zfmisc_1(A_446,D_443)))
      | ~ m1_subset_1(F_447,k1_zfmisc_1(k2_zfmisc_1(C_448,D_443)))
      | ~ v1_funct_1(F_447)
      | ~ m1_subset_1(E_445,k1_zfmisc_1(k2_zfmisc_1(A_446,B_444)))
      | ~ v1_funct_1(E_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2911,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2740,c_2854])).

tff(c_2943,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_88,c_84,c_2911])).

tff(c_2945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2747,c_2943])).

tff(c_2946,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2535])).

tff(c_3051,plain,(
    ! [D_471,E_468,B_467,A_466,F_469,C_470] :
      ( k1_partfun1(A_466,B_467,C_470,D_471,E_468,F_469) = k5_relat_1(E_468,F_469)
      | ~ m1_subset_1(F_469,k1_zfmisc_1(k2_zfmisc_1(C_470,D_471)))
      | ~ v1_funct_1(F_469)
      | ~ m1_subset_1(E_468,k1_zfmisc_1(k2_zfmisc_1(A_466,B_467)))
      | ~ v1_funct_1(E_468) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_3055,plain,(
    ! [A_466,B_467,E_468] :
      ( k1_partfun1(A_466,B_467,'#skF_2','#skF_1',E_468,'#skF_4') = k5_relat_1(E_468,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_468,k1_zfmisc_1(k2_zfmisc_1(A_466,B_467)))
      | ~ v1_funct_1(E_468) ) ),
    inference(resolution,[status(thm)],[c_84,c_3051])).

tff(c_3066,plain,(
    ! [A_473,B_474,E_475] :
      ( k1_partfun1(A_473,B_474,'#skF_2','#skF_1',E_475,'#skF_4') = k5_relat_1(E_475,'#skF_4')
      | ~ m1_subset_1(E_475,k1_zfmisc_1(k2_zfmisc_1(A_473,B_474)))
      | ~ v1_funct_1(E_475) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3055])).

tff(c_3075,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_3066])).

tff(c_3082,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2946,c_3075])).

tff(c_14,plain,(
    ! [A_8,B_10] :
      ( v2_funct_1(A_8)
      | k2_relat_1(B_10) != k1_relat_1(A_8)
      | ~ v2_funct_1(k5_relat_1(B_10,A_8))
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3089,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3082,c_14])).

tff(c_3095,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_88,c_154,c_94,c_96,c_2358,c_2467,c_3089])).

tff(c_3097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2996,c_3095])).

tff(c_3099,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2967])).

tff(c_3100,plain,(
    ! [B_476] :
      ( k2_funct_1('#skF_4') = B_476
      | k5_relat_1(B_476,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_476) != '#skF_2'
      | ~ v1_funct_1(B_476)
      | ~ v1_relat_1(B_476) ) ),
    inference(splitRight,[status(thm)],[c_2967])).

tff(c_3103,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_154,c_3100])).

tff(c_3115,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2358,c_3103])).

tff(c_3122,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3115])).

tff(c_3183,plain,(
    ! [E_493,A_491,B_492,D_496,C_495,F_494] :
      ( k1_partfun1(A_491,B_492,C_495,D_496,E_493,F_494) = k5_relat_1(E_493,F_494)
      | ~ m1_subset_1(F_494,k1_zfmisc_1(k2_zfmisc_1(C_495,D_496)))
      | ~ v1_funct_1(F_494)
      | ~ m1_subset_1(E_493,k1_zfmisc_1(k2_zfmisc_1(A_491,B_492)))
      | ~ v1_funct_1(E_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_3187,plain,(
    ! [A_491,B_492,E_493] :
      ( k1_partfun1(A_491,B_492,'#skF_2','#skF_1',E_493,'#skF_4') = k5_relat_1(E_493,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_493,k1_zfmisc_1(k2_zfmisc_1(A_491,B_492)))
      | ~ v1_funct_1(E_493) ) ),
    inference(resolution,[status(thm)],[c_84,c_3183])).

tff(c_3198,plain,(
    ! [A_498,B_499,E_500] :
      ( k1_partfun1(A_498,B_499,'#skF_2','#skF_1',E_500,'#skF_4') = k5_relat_1(E_500,'#skF_4')
      | ~ m1_subset_1(E_500,k1_zfmisc_1(k2_zfmisc_1(A_498,B_499)))
      | ~ v1_funct_1(E_500) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3187])).

tff(c_3207,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_3198])).

tff(c_3214,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2946,c_3207])).

tff(c_3216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3122,c_3214])).

tff(c_3217,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3115])).

tff(c_24,plain,(
    ! [A_15] :
      ( k2_funct_1(k2_funct_1(A_15)) = A_15
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3229,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3217,c_24])).

tff(c_3237,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_88,c_3099,c_3229])).

tff(c_3239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:50:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.81/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.81/2.13  
% 5.81/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.00/2.13  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.00/2.13  
% 6.00/2.13  %Foreground sorts:
% 6.00/2.13  
% 6.00/2.13  
% 6.00/2.13  %Background operators:
% 6.00/2.13  
% 6.00/2.13  
% 6.00/2.13  %Foreground operators:
% 6.00/2.13  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.00/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.00/2.13  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.00/2.13  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.00/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.00/2.13  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.00/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.00/2.13  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.00/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.00/2.13  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.00/2.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.00/2.13  tff('#skF_2', type, '#skF_2': $i).
% 6.00/2.13  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.00/2.13  tff('#skF_3', type, '#skF_3': $i).
% 6.00/2.13  tff('#skF_1', type, '#skF_1': $i).
% 6.00/2.13  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.00/2.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.00/2.13  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.00/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.00/2.13  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.00/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.00/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.00/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.00/2.13  tff('#skF_4', type, '#skF_4': $i).
% 6.00/2.13  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.00/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.00/2.13  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.00/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.00/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.00/2.13  
% 6.08/2.17  tff(f_227, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 6.08/2.17  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.08/2.17  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.08/2.17  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.08/2.17  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.08/2.17  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.08/2.17  tff(f_138, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.08/2.17  tff(f_154, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.08/2.17  tff(f_112, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.08/2.17  tff(f_164, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.08/2.17  tff(f_150, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.08/2.17  tff(f_185, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 6.08/2.17  tff(f_166, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.08/2.17  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 6.08/2.17  tff(f_42, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.08/2.17  tff(f_38, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.08/2.17  tff(f_201, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 6.08/2.17  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 6.08/2.17  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 6.08/2.17  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 6.08/2.17  tff(c_72, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_227])).
% 6.08/2.17  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.08/2.17  tff(c_84, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_227])).
% 6.08/2.17  tff(c_136, plain, (![B_63, A_64]: (v1_relat_1(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.08/2.17  tff(c_142, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_84, c_136])).
% 6.08/2.17  tff(c_151, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_142])).
% 6.08/2.17  tff(c_88, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_227])).
% 6.08/2.17  tff(c_76, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_227])).
% 6.08/2.17  tff(c_86, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 6.08/2.17  tff(c_2371, plain, (![A_357, B_358, C_359]: (k1_relset_1(A_357, B_358, C_359)=k1_relat_1(C_359) | ~m1_subset_1(C_359, k1_zfmisc_1(k2_zfmisc_1(A_357, B_358))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.08/2.17  tff(c_2383, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_2371])).
% 6.08/2.17  tff(c_2452, plain, (![B_370, A_371, C_372]: (k1_xboole_0=B_370 | k1_relset_1(A_371, B_370, C_372)=A_371 | ~v1_funct_2(C_372, A_371, B_370) | ~m1_subset_1(C_372, k1_zfmisc_1(k2_zfmisc_1(A_371, B_370))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.08/2.17  tff(c_2458, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_2452])).
% 6.08/2.17  tff(c_2466, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2383, c_2458])).
% 6.08/2.17  tff(c_2467, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_76, c_2466])).
% 6.08/2.17  tff(c_168, plain, (![C_68, B_69, A_70]: (v5_relat_1(C_68, B_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.08/2.17  tff(c_179, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_168])).
% 6.08/2.17  tff(c_209, plain, (![B_76, A_77]: (k2_relat_1(B_76)=A_77 | ~v2_funct_2(B_76, A_77) | ~v5_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.08/2.17  tff(c_218, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_179, c_209])).
% 6.08/2.17  tff(c_227, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_218])).
% 6.08/2.17  tff(c_238, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_227])).
% 6.08/2.17  tff(c_94, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_227])).
% 6.08/2.17  tff(c_92, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 6.08/2.17  tff(c_90, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_227])).
% 6.08/2.17  tff(c_58, plain, (![A_37]: (m1_subset_1(k6_partfun1(A_37), k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.08/2.17  tff(c_228, plain, (![A_78, B_79, D_80]: (r2_relset_1(A_78, B_79, D_80, D_80) | ~m1_subset_1(D_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.08/2.17  tff(c_235, plain, (![A_37]: (r2_relset_1(A_37, A_37, k6_partfun1(A_37), k6_partfun1(A_37)))), inference(resolution, [status(thm)], [c_58, c_228])).
% 6.08/2.17  tff(c_877, plain, (![C_200, F_199, E_198, D_201, B_197, A_196]: (k1_partfun1(A_196, B_197, C_200, D_201, E_198, F_199)=k5_relat_1(E_198, F_199) | ~m1_subset_1(F_199, k1_zfmisc_1(k2_zfmisc_1(C_200, D_201))) | ~v1_funct_1(F_199) | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~v1_funct_1(E_198))), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.08/2.17  tff(c_881, plain, (![A_196, B_197, E_198]: (k1_partfun1(A_196, B_197, '#skF_2', '#skF_1', E_198, '#skF_4')=k5_relat_1(E_198, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~v1_funct_1(E_198))), inference(resolution, [status(thm)], [c_84, c_877])).
% 6.08/2.17  tff(c_955, plain, (![A_213, B_214, E_215]: (k1_partfun1(A_213, B_214, '#skF_2', '#skF_1', E_215, '#skF_4')=k5_relat_1(E_215, '#skF_4') | ~m1_subset_1(E_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))) | ~v1_funct_1(E_215))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_881])).
% 6.08/2.17  tff(c_964, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_955])).
% 6.08/2.17  tff(c_971, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_964])).
% 6.08/2.17  tff(c_80, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 6.08/2.17  tff(c_747, plain, (![D_166, C_167, A_168, B_169]: (D_166=C_167 | ~r2_relset_1(A_168, B_169, C_167, D_166) | ~m1_subset_1(D_166, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.08/2.17  tff(c_755, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_80, c_747])).
% 6.08/2.17  tff(c_770, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_755])).
% 6.08/2.17  tff(c_771, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_770])).
% 6.08/2.17  tff(c_978, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_971, c_771])).
% 6.08/2.17  tff(c_1040, plain, (![F_228, B_225, C_229, D_224, A_227, E_226]: (m1_subset_1(k1_partfun1(A_227, B_225, C_229, D_224, E_226, F_228), k1_zfmisc_1(k2_zfmisc_1(A_227, D_224))) | ~m1_subset_1(F_228, k1_zfmisc_1(k2_zfmisc_1(C_229, D_224))) | ~v1_funct_1(F_228) | ~m1_subset_1(E_226, k1_zfmisc_1(k2_zfmisc_1(A_227, B_225))) | ~v1_funct_1(E_226))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.08/2.17  tff(c_1097, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_971, c_1040])).
% 6.08/2.17  tff(c_1129, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_88, c_84, c_1097])).
% 6.08/2.17  tff(c_1131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_978, c_1129])).
% 6.08/2.17  tff(c_1132, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_770])).
% 6.08/2.17  tff(c_1931, plain, (![D_286, A_287, B_288, C_289]: (v2_funct_2(D_286, A_287) | ~r2_relset_1(A_287, A_287, k1_partfun1(A_287, B_288, B_288, A_287, C_289, D_286), k6_partfun1(A_287)) | ~m1_subset_1(D_286, k1_zfmisc_1(k2_zfmisc_1(B_288, A_287))) | ~v1_funct_2(D_286, B_288, A_287) | ~v1_funct_1(D_286) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))) | ~v1_funct_2(C_289, A_287, B_288) | ~v1_funct_1(C_289))), inference(cnfTransformation, [status(thm)], [f_185])).
% 6.08/2.17  tff(c_1937, plain, (v2_funct_2('#skF_4', '#skF_1') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1132, c_1931])).
% 6.08/2.17  tff(c_1941, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_90, c_88, c_86, c_84, c_235, c_1937])).
% 6.08/2.17  tff(c_1943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_238, c_1941])).
% 6.08/2.17  tff(c_1944, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_227])).
% 6.08/2.17  tff(c_62, plain, (![A_44]: (k6_relat_1(A_44)=k6_partfun1(A_44))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.08/2.17  tff(c_22, plain, (![A_12, B_14]: (k2_funct_1(A_12)=B_14 | k6_relat_1(k2_relat_1(A_12))!=k5_relat_1(B_14, A_12) | k2_relat_1(B_14)!=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.08/2.17  tff(c_2955, plain, (![A_449, B_450]: (k2_funct_1(A_449)=B_450 | k6_partfun1(k2_relat_1(A_449))!=k5_relat_1(B_450, A_449) | k2_relat_1(B_450)!=k1_relat_1(A_449) | ~v2_funct_1(A_449) | ~v1_funct_1(B_450) | ~v1_relat_1(B_450) | ~v1_funct_1(A_449) | ~v1_relat_1(A_449))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_22])).
% 6.08/2.17  tff(c_2961, plain, (![B_450]: (k2_funct_1('#skF_4')=B_450 | k5_relat_1(B_450, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_450)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_450) | ~v1_relat_1(B_450) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1944, c_2955])).
% 6.08/2.17  tff(c_2967, plain, (![B_450]: (k2_funct_1('#skF_4')=B_450 | k5_relat_1(B_450, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_450)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_450) | ~v1_relat_1(B_450))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_88, c_2467, c_2961])).
% 6.08/2.17  tff(c_2996, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2967])).
% 6.08/2.17  tff(c_145, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_90, c_136])).
% 6.08/2.17  tff(c_154, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_145])).
% 6.08/2.17  tff(c_12, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.08/2.17  tff(c_96, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_12])).
% 6.08/2.17  tff(c_180, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_90, c_168])).
% 6.08/2.17  tff(c_215, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_180, c_209])).
% 6.08/2.17  tff(c_224, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_215])).
% 6.08/2.17  tff(c_1956, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_224])).
% 6.08/2.17  tff(c_78, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_227])).
% 6.08/2.17  tff(c_6, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.08/2.17  tff(c_99, plain, (![A_6]: (k1_relat_1(k6_partfun1(A_6))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_6])).
% 6.08/2.17  tff(c_74, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_227])).
% 6.08/2.17  tff(c_82, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_227])).
% 6.08/2.17  tff(c_2298, plain, (![B_353, C_354, A_355]: (k6_partfun1(B_353)=k5_relat_1(k2_funct_1(C_354), C_354) | k1_xboole_0=B_353 | ~v2_funct_1(C_354) | k2_relset_1(A_355, B_353, C_354)!=B_353 | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(A_355, B_353))) | ~v1_funct_2(C_354, A_355, B_353) | ~v1_funct_1(C_354))), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.08/2.17  tff(c_2304, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_2298])).
% 6.08/2.17  tff(c_2314, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_78, c_2304])).
% 6.08/2.17  tff(c_2315, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_74, c_2314])).
% 6.08/2.17  tff(c_20, plain, (![A_11]: (k1_relat_1(k5_relat_1(k2_funct_1(A_11), A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.08/2.17  tff(c_2327, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2315, c_20])).
% 6.08/2.17  tff(c_2340, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_94, c_78, c_99, c_2327])).
% 6.08/2.17  tff(c_48, plain, (![B_30]: (v2_funct_2(B_30, k2_relat_1(B_30)) | ~v5_relat_1(B_30, k2_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.08/2.17  tff(c_2349, plain, (v2_funct_2('#skF_3', k2_relat_1('#skF_3')) | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2340, c_48])).
% 6.08/2.17  tff(c_2355, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_180, c_2340, c_2349])).
% 6.08/2.17  tff(c_2357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1956, c_2355])).
% 6.08/2.17  tff(c_2358, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_224])).
% 6.08/2.17  tff(c_2646, plain, (![D_416, E_413, F_414, A_411, C_415, B_412]: (k1_partfun1(A_411, B_412, C_415, D_416, E_413, F_414)=k5_relat_1(E_413, F_414) | ~m1_subset_1(F_414, k1_zfmisc_1(k2_zfmisc_1(C_415, D_416))) | ~v1_funct_1(F_414) | ~m1_subset_1(E_413, k1_zfmisc_1(k2_zfmisc_1(A_411, B_412))) | ~v1_funct_1(E_413))), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.08/2.17  tff(c_2650, plain, (![A_411, B_412, E_413]: (k1_partfun1(A_411, B_412, '#skF_2', '#skF_1', E_413, '#skF_4')=k5_relat_1(E_413, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_413, k1_zfmisc_1(k2_zfmisc_1(A_411, B_412))) | ~v1_funct_1(E_413))), inference(resolution, [status(thm)], [c_84, c_2646])).
% 6.08/2.17  tff(c_2724, plain, (![A_428, B_429, E_430]: (k1_partfun1(A_428, B_429, '#skF_2', '#skF_1', E_430, '#skF_4')=k5_relat_1(E_430, '#skF_4') | ~m1_subset_1(E_430, k1_zfmisc_1(k2_zfmisc_1(A_428, B_429))) | ~v1_funct_1(E_430))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2650])).
% 6.08/2.17  tff(c_2733, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_2724])).
% 6.08/2.17  tff(c_2740, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2733])).
% 6.08/2.17  tff(c_2512, plain, (![D_381, C_382, A_383, B_384]: (D_381=C_382 | ~r2_relset_1(A_383, B_384, C_382, D_381) | ~m1_subset_1(D_381, k1_zfmisc_1(k2_zfmisc_1(A_383, B_384))) | ~m1_subset_1(C_382, k1_zfmisc_1(k2_zfmisc_1(A_383, B_384))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.08/2.17  tff(c_2520, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_80, c_2512])).
% 6.08/2.17  tff(c_2535, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2520])).
% 6.08/2.17  tff(c_2536, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2535])).
% 6.08/2.17  tff(c_2747, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2740, c_2536])).
% 6.08/2.17  tff(c_2854, plain, (![C_448, D_443, F_447, B_444, E_445, A_446]: (m1_subset_1(k1_partfun1(A_446, B_444, C_448, D_443, E_445, F_447), k1_zfmisc_1(k2_zfmisc_1(A_446, D_443))) | ~m1_subset_1(F_447, k1_zfmisc_1(k2_zfmisc_1(C_448, D_443))) | ~v1_funct_1(F_447) | ~m1_subset_1(E_445, k1_zfmisc_1(k2_zfmisc_1(A_446, B_444))) | ~v1_funct_1(E_445))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.08/2.17  tff(c_2911, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2740, c_2854])).
% 6.08/2.17  tff(c_2943, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_88, c_84, c_2911])).
% 6.08/2.17  tff(c_2945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2747, c_2943])).
% 6.08/2.17  tff(c_2946, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2535])).
% 6.08/2.17  tff(c_3051, plain, (![D_471, E_468, B_467, A_466, F_469, C_470]: (k1_partfun1(A_466, B_467, C_470, D_471, E_468, F_469)=k5_relat_1(E_468, F_469) | ~m1_subset_1(F_469, k1_zfmisc_1(k2_zfmisc_1(C_470, D_471))) | ~v1_funct_1(F_469) | ~m1_subset_1(E_468, k1_zfmisc_1(k2_zfmisc_1(A_466, B_467))) | ~v1_funct_1(E_468))), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.08/2.17  tff(c_3055, plain, (![A_466, B_467, E_468]: (k1_partfun1(A_466, B_467, '#skF_2', '#skF_1', E_468, '#skF_4')=k5_relat_1(E_468, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_468, k1_zfmisc_1(k2_zfmisc_1(A_466, B_467))) | ~v1_funct_1(E_468))), inference(resolution, [status(thm)], [c_84, c_3051])).
% 6.08/2.17  tff(c_3066, plain, (![A_473, B_474, E_475]: (k1_partfun1(A_473, B_474, '#skF_2', '#skF_1', E_475, '#skF_4')=k5_relat_1(E_475, '#skF_4') | ~m1_subset_1(E_475, k1_zfmisc_1(k2_zfmisc_1(A_473, B_474))) | ~v1_funct_1(E_475))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_3055])).
% 6.08/2.17  tff(c_3075, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_3066])).
% 6.08/2.17  tff(c_3082, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2946, c_3075])).
% 6.08/2.17  tff(c_14, plain, (![A_8, B_10]: (v2_funct_1(A_8) | k2_relat_1(B_10)!=k1_relat_1(A_8) | ~v2_funct_1(k5_relat_1(B_10, A_8)) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.08/2.17  tff(c_3089, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3082, c_14])).
% 6.08/2.17  tff(c_3095, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_88, c_154, c_94, c_96, c_2358, c_2467, c_3089])).
% 6.08/2.17  tff(c_3097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2996, c_3095])).
% 6.08/2.17  tff(c_3099, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2967])).
% 6.08/2.17  tff(c_3100, plain, (![B_476]: (k2_funct_1('#skF_4')=B_476 | k5_relat_1(B_476, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_476)!='#skF_2' | ~v1_funct_1(B_476) | ~v1_relat_1(B_476))), inference(splitRight, [status(thm)], [c_2967])).
% 6.08/2.17  tff(c_3103, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_154, c_3100])).
% 6.08/2.17  tff(c_3115, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2358, c_3103])).
% 6.08/2.17  tff(c_3122, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_3115])).
% 6.08/2.17  tff(c_3183, plain, (![E_493, A_491, B_492, D_496, C_495, F_494]: (k1_partfun1(A_491, B_492, C_495, D_496, E_493, F_494)=k5_relat_1(E_493, F_494) | ~m1_subset_1(F_494, k1_zfmisc_1(k2_zfmisc_1(C_495, D_496))) | ~v1_funct_1(F_494) | ~m1_subset_1(E_493, k1_zfmisc_1(k2_zfmisc_1(A_491, B_492))) | ~v1_funct_1(E_493))), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.08/2.17  tff(c_3187, plain, (![A_491, B_492, E_493]: (k1_partfun1(A_491, B_492, '#skF_2', '#skF_1', E_493, '#skF_4')=k5_relat_1(E_493, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_493, k1_zfmisc_1(k2_zfmisc_1(A_491, B_492))) | ~v1_funct_1(E_493))), inference(resolution, [status(thm)], [c_84, c_3183])).
% 6.08/2.17  tff(c_3198, plain, (![A_498, B_499, E_500]: (k1_partfun1(A_498, B_499, '#skF_2', '#skF_1', E_500, '#skF_4')=k5_relat_1(E_500, '#skF_4') | ~m1_subset_1(E_500, k1_zfmisc_1(k2_zfmisc_1(A_498, B_499))) | ~v1_funct_1(E_500))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_3187])).
% 6.08/2.17  tff(c_3207, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_3198])).
% 6.08/2.17  tff(c_3214, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2946, c_3207])).
% 6.08/2.17  tff(c_3216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3122, c_3214])).
% 6.08/2.17  tff(c_3217, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_3115])).
% 6.08/2.17  tff(c_24, plain, (![A_15]: (k2_funct_1(k2_funct_1(A_15))=A_15 | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.08/2.17  tff(c_3229, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3217, c_24])).
% 6.08/2.17  tff(c_3237, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_151, c_88, c_3099, c_3229])).
% 6.08/2.17  tff(c_3239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_3237])).
% 6.08/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.08/2.17  
% 6.08/2.17  Inference rules
% 6.08/2.17  ----------------------
% 6.08/2.17  #Ref     : 0
% 6.08/2.17  #Sup     : 666
% 6.08/2.17  #Fact    : 0
% 6.08/2.17  #Define  : 0
% 6.08/2.17  #Split   : 29
% 6.08/2.17  #Chain   : 0
% 6.08/2.17  #Close   : 0
% 6.08/2.17  
% 6.08/2.17  Ordering : KBO
% 6.08/2.17  
% 6.08/2.17  Simplification rules
% 6.08/2.17  ----------------------
% 6.08/2.17  #Subsume      : 23
% 6.08/2.17  #Demod        : 688
% 6.08/2.17  #Tautology    : 224
% 6.08/2.17  #SimpNegUnit  : 62
% 6.08/2.17  #BackRed      : 36
% 6.08/2.17  
% 6.08/2.17  #Partial instantiations: 0
% 6.08/2.17  #Strategies tried      : 1
% 6.08/2.17  
% 6.08/2.17  Timing (in seconds)
% 6.08/2.17  ----------------------
% 6.08/2.17  Preprocessing        : 0.39
% 6.08/2.17  Parsing              : 0.21
% 6.08/2.17  CNF conversion       : 0.03
% 6.08/2.17  Main loop            : 0.96
% 6.08/2.17  Inferencing          : 0.34
% 6.08/2.17  Reduction            : 0.33
% 6.08/2.17  Demodulation         : 0.24
% 6.08/2.17  BG Simplification    : 0.04
% 6.08/2.17  Subsumption          : 0.17
% 6.08/2.17  Abstraction          : 0.04
% 6.08/2.17  MUC search           : 0.00
% 6.08/2.17  Cooper               : 0.00
% 6.08/2.17  Total                : 1.43
% 6.08/2.17  Index Insertion      : 0.00
% 6.08/2.17  Index Deletion       : 0.00
% 6.08/2.17  Index Matching       : 0.00
% 6.08/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
