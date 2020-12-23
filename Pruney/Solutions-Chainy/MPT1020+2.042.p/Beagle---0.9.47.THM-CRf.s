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
% DateTime   : Thu Dec  3 10:15:56 EST 2020

% Result     : Theorem 4.73s
% Output     : CNFRefutation 5.10s
% Verified   : 
% Statistics : Number of formulae       :  201 (2959 expanded)
%              Number of leaves         :   42 ( 967 expanded)
%              Depth                    :   20
%              Number of atoms          :  389 (7714 expanded)
%              Number of equality atoms :  125 (2542 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_181,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_115,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_37,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_83,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_159,axiom,(
    ! [A,B,C] :
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

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_287,plain,(
    ! [A_67,B_68,D_69] :
      ( r2_relset_1(A_67,B_68,D_69,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_298,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_287])).

tff(c_46,plain,(
    ! [A_26] : k6_relat_1(A_26) = k6_partfun1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_8,plain,(
    ! [A_2] : k2_relat_1(k6_relat_1(A_2)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ! [A_2] : k2_relat_1(k6_partfun1(A_2)) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_32,plain,(
    ! [A_18] : m1_subset_1(k6_relat_1(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_73,plain,(
    ! [A_18] : m1_subset_1(k6_partfun1(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_32])).

tff(c_106,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_135,plain,(
    ! [A_47] : v1_relat_1(k6_partfun1(A_47)) ),
    inference(resolution,[status(thm)],[c_73,c_106])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_138,plain,(
    ! [A_47] :
      ( k2_relat_1(k6_partfun1(A_47)) != k1_xboole_0
      | k6_partfun1(A_47) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_148,plain,(
    ! [A_48] :
      ( k1_xboole_0 != A_48
      | k6_partfun1(A_48) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_138])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_154,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_56])).

tff(c_203,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_72,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_70,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_66,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_118,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_106])).

tff(c_237,plain,(
    ! [C_58,B_59,A_60] :
      ( v5_relat_1(C_58,B_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_253,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_237])).

tff(c_331,plain,(
    ! [B_76,A_77] :
      ( k2_relat_1(B_76) = A_77
      | ~ v2_funct_2(B_76,A_77)
      | ~ v5_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_340,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_253,c_331])).

tff(c_352,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_340])).

tff(c_368,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_352])).

tff(c_68,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_582,plain,(
    ! [C_101,B_102,A_103] :
      ( v2_funct_2(C_101,B_102)
      | ~ v3_funct_2(C_101,A_103,B_102)
      | ~ v1_funct_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_594,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_582])).

tff(c_603,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_594])).

tff(c_605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_368,c_603])).

tff(c_606,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_725,plain,(
    ! [A_115,B_116,C_117] :
      ( k2_relset_1(A_115,B_116,C_117) = k2_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_737,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_725])).

tff(c_745,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_737])).

tff(c_750,plain,(
    ! [C_118,A_119,B_120] :
      ( v2_funct_1(C_118)
      | ~ v3_funct_2(C_118,A_119,B_120)
      | ~ v1_funct_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_762,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_750])).

tff(c_770,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_762])).

tff(c_1059,plain,(
    ! [C_156,D_157,B_158,A_159] :
      ( k2_funct_1(C_156) = D_157
      | k1_xboole_0 = B_158
      | k1_xboole_0 = A_159
      | ~ v2_funct_1(C_156)
      | ~ r2_relset_1(A_159,A_159,k1_partfun1(A_159,B_158,B_158,A_159,C_156,D_157),k6_partfun1(A_159))
      | k2_relset_1(A_159,B_158,C_156) != B_158
      | ~ m1_subset_1(D_157,k1_zfmisc_1(k2_zfmisc_1(B_158,A_159)))
      | ~ v1_funct_2(D_157,B_158,A_159)
      | ~ v1_funct_1(D_157)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_159,B_158)))
      | ~ v1_funct_2(C_156,A_159,B_158)
      | ~ v1_funct_1(C_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1065,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1059])).

tff(c_1068,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_58,c_745,c_770,c_1065])).

tff(c_1069,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_1068])).

tff(c_921,plain,(
    ! [A_138,B_139] :
      ( k2_funct_2(A_138,B_139) = k2_funct_1(B_139)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k2_zfmisc_1(A_138,A_138)))
      | ~ v3_funct_2(B_139,A_138,A_138)
      | ~ v1_funct_2(B_139,A_138,A_138)
      | ~ v1_funct_1(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_933,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_921])).

tff(c_941,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_933])).

tff(c_54,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_946,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_54])).

tff(c_1070,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1069,c_946])).

tff(c_1074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_1070])).

tff(c_1076,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_117,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_106])).

tff(c_125,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_117,c_2])).

tff(c_146,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_1079,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1076,c_146])).

tff(c_1087,plain,(
    ! [C_161,B_162,A_163] :
      ( v5_relat_1(C_161,B_162)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_163,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1098,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_1087])).

tff(c_1244,plain,(
    ! [B_178,A_179] :
      ( k2_relat_1(B_178) = A_179
      | ~ v2_funct_2(B_178,A_179)
      | ~ v5_relat_1(B_178,A_179)
      | ~ v1_relat_1(B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1256,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1098,c_1244])).

tff(c_1269,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_1256])).

tff(c_1270,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1079,c_1269])).

tff(c_60,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1418,plain,(
    ! [C_200,B_201,A_202] :
      ( v2_funct_2(C_200,B_201)
      | ~ v3_funct_2(C_200,A_202,B_201)
      | ~ v1_funct_1(C_200)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_202,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1427,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1418])).

tff(c_1436,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_1427])).

tff(c_1438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1270,c_1436])).

tff(c_1439,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_143,plain,(
    ! [A_47] :
      ( k1_xboole_0 != A_47
      | k6_partfun1(A_47) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_138])).

tff(c_1454,plain,(
    ! [A_203] :
      ( A_203 != '#skF_3'
      | k6_partfun1(A_203) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1439,c_1439,c_143])).

tff(c_1460,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_3')
    | '#skF_3' != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1454,c_56])).

tff(c_1498,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1460])).

tff(c_1440,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_1447,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1439,c_1440])).

tff(c_1533,plain,(
    ! [C_212,B_213,A_214] :
      ( v5_relat_1(C_212,B_213)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_214,B_213))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1544,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_1533])).

tff(c_1638,plain,(
    ! [B_228,A_229] :
      ( k2_relat_1(B_228) = A_229
      | ~ v2_funct_2(B_228,A_229)
      | ~ v5_relat_1(B_228,A_229)
      | ~ v1_relat_1(B_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1650,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1544,c_1638])).

tff(c_1662,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_1447,c_1650])).

tff(c_1663,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1498,c_1662])).

tff(c_1811,plain,(
    ! [C_246,B_247,A_248] :
      ( v2_funct_2(C_246,B_247)
      | ~ v3_funct_2(C_246,A_248,B_247)
      | ~ v1_funct_1(C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_248,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1820,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1811])).

tff(c_1831,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_1820])).

tff(c_1833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1663,c_1831])).

tff(c_1835,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1460])).

tff(c_6,plain,(
    ! [A_2] : k1_relat_1(k6_relat_1(A_2)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_75,plain,(
    ! [A_2] : k1_relat_1(k6_partfun1(A_2)) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6])).

tff(c_1468,plain,(
    ! [A_203] :
      ( k1_relat_1('#skF_3') = A_203
      | A_203 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1454,c_75])).

tff(c_2253,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1835,c_1835,c_1468])).

tff(c_1840,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1835,c_1439])).

tff(c_133,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_118,c_2])).

tff(c_1861,plain,
    ( k2_relat_1('#skF_2') != '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1840,c_1840,c_133])).

tff(c_1862,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1861])).

tff(c_1972,plain,(
    ! [C_258,B_259,A_260] :
      ( v5_relat_1(C_258,B_259)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_260,B_259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1984,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_1972])).

tff(c_2042,plain,(
    ! [B_268,A_269] :
      ( k2_relat_1(B_268) = A_269
      | ~ v2_funct_2(B_268,A_269)
      | ~ v5_relat_1(B_268,A_269)
      | ~ v1_relat_1(B_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2051,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1984,c_2042])).

tff(c_2060,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_2051])).

tff(c_2061,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1862,c_2060])).

tff(c_2171,plain,(
    ! [C_286,B_287,A_288] :
      ( v2_funct_2(C_286,B_287)
      | ~ v3_funct_2(C_286,A_288,B_287)
      | ~ v1_funct_1(C_286)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_288,B_287))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2180,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_2171])).

tff(c_2188,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_2180])).

tff(c_2190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2061,c_2188])).

tff(c_2191,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1861])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_134,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_118,c_4])).

tff(c_1479,plain,
    ( k1_relat_1('#skF_2') != '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1439,c_1439,c_134])).

tff(c_1480,plain,(
    k1_relat_1('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1479])).

tff(c_1837,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1835,c_1480])).

tff(c_2193,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2191,c_1837])).

tff(c_2256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2253,c_2193])).

tff(c_2257,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1479])).

tff(c_2389,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_3'),'#skF_3')
    | '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2257,c_1460])).

tff(c_2390,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2389])).

tff(c_2301,plain,(
    ! [C_296,B_297,A_298] :
      ( v5_relat_1(C_296,B_297)
      | ~ m1_subset_1(C_296,k1_zfmisc_1(k2_zfmisc_1(A_298,B_297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2309,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_2301])).

tff(c_2448,plain,(
    ! [B_319,A_320] :
      ( k2_relat_1(B_319) = A_320
      | ~ v2_funct_2(B_319,A_320)
      | ~ v5_relat_1(B_319,A_320)
      | ~ v1_relat_1(B_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2457,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2309,c_2448])).

tff(c_2466,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_1447,c_2457])).

tff(c_2467,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2390,c_2466])).

tff(c_2521,plain,(
    ! [C_328,B_329,A_330] :
      ( v2_funct_2(C_328,B_329)
      | ~ v3_funct_2(C_328,A_330,B_329)
      | ~ v1_funct_1(C_328)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_330,B_329))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2530,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2521])).

tff(c_2538,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2530])).

tff(c_2540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2467,c_2538])).

tff(c_2542,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2389])).

tff(c_1465,plain,(
    ! [A_203] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_203,A_203)))
      | A_203 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1454,c_73])).

tff(c_2544,plain,(
    ! [A_203] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_203,A_203)))
      | A_203 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2542,c_2542,c_1465])).

tff(c_2743,plain,(
    ! [A_343,B_344,D_345] :
      ( r2_relset_1(A_343,B_344,D_345,D_345)
      | ~ m1_subset_1(D_345,k1_zfmisc_1(k2_zfmisc_1(A_343,B_344))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2758,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2544,c_2743])).

tff(c_2560,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2542,c_62])).

tff(c_2561,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2542,c_60])).

tff(c_2562,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2542,c_64])).

tff(c_2558,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2542,c_117])).

tff(c_2832,plain,(
    ! [C_358,A_359,B_360] :
      ( v2_funct_1(C_358)
      | ~ v3_funct_2(C_358,A_359,B_360)
      | ~ v1_funct_1(C_358)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_359,B_360))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2835,plain,(
    ! [A_203] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_203,A_203)
      | ~ v1_funct_1('#skF_1')
      | A_203 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_2544,c_2832])).

tff(c_2841,plain,(
    ! [A_203] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_203,A_203)
      | A_203 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2562,c_2835])).

tff(c_2856,plain,(
    ~ v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2841])).

tff(c_2858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2856,c_2561])).

tff(c_2859,plain,(
    v2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2841])).

tff(c_2258,plain,(
    k1_relat_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1479])).

tff(c_2284,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2257,c_2258])).

tff(c_2552,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2542,c_2542,c_2284])).

tff(c_16,plain,(
    ! [A_4] :
      ( k2_relat_1(k2_funct_1(A_4)) = k1_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2359,plain,(
    ! [A_304] :
      ( v1_relat_1(k2_funct_1(A_304))
      | ~ v2_funct_1(A_304)
      | ~ v1_funct_1(A_304)
      | ~ v1_relat_1(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1441,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != '#skF_3'
      | A_1 = '#skF_3'
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1439,c_1439,c_2])).

tff(c_2366,plain,(
    ! [A_304] :
      ( k2_relat_1(k2_funct_1(A_304)) != '#skF_3'
      | k2_funct_1(A_304) = '#skF_3'
      | ~ v2_funct_1(A_304)
      | ~ v1_funct_1(A_304)
      | ~ v1_relat_1(A_304) ) ),
    inference(resolution,[status(thm)],[c_2359,c_1441])).

tff(c_2828,plain,(
    ! [A_357] :
      ( k2_relat_1(k2_funct_1(A_357)) != '#skF_1'
      | k2_funct_1(A_357) = '#skF_1'
      | ~ v2_funct_1(A_357)
      | ~ v1_funct_1(A_357)
      | ~ v1_relat_1(A_357) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2542,c_2542,c_2366])).

tff(c_2897,plain,(
    ! [A_370] :
      ( k1_relat_1(A_370) != '#skF_1'
      | k2_funct_1(A_370) = '#skF_1'
      | ~ v2_funct_1(A_370)
      | ~ v1_funct_1(A_370)
      | ~ v1_relat_1(A_370)
      | ~ v2_funct_1(A_370)
      | ~ v1_funct_1(A_370)
      | ~ v1_relat_1(A_370) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2828])).

tff(c_2899,plain,
    ( k1_relat_1('#skF_1') != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1'
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2859,c_2897])).

tff(c_2904,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2562,c_2859,c_2552,c_2899])).

tff(c_2954,plain,(
    ! [A_372,B_373] :
      ( k2_funct_2(A_372,B_373) = k2_funct_1(B_373)
      | ~ m1_subset_1(B_373,k1_zfmisc_1(k2_zfmisc_1(A_372,A_372)))
      | ~ v3_funct_2(B_373,A_372,A_372)
      | ~ v1_funct_2(B_373,A_372,A_372)
      | ~ v1_funct_1(B_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2957,plain,(
    ! [A_203] :
      ( k2_funct_2(A_203,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_203,A_203)
      | ~ v1_funct_2('#skF_1',A_203,A_203)
      | ~ v1_funct_1('#skF_1')
      | A_203 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_2544,c_2954])).

tff(c_2966,plain,(
    ! [A_374] :
      ( k2_funct_2(A_374,'#skF_1') = '#skF_1'
      | ~ v3_funct_2('#skF_1',A_374,A_374)
      | ~ v1_funct_2('#skF_1',A_374,A_374)
      | A_374 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2562,c_2904,c_2957])).

tff(c_2969,plain,
    ( k2_funct_2('#skF_1','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2561,c_2966])).

tff(c_2972,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_2969])).

tff(c_2261,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2257,c_54])).

tff(c_2551,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2542,c_2542,c_2261])).

tff(c_2973,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2972,c_2551])).

tff(c_2976,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2758,c_2973])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.73/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.92  
% 5.10/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.92  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.10/1.92  
% 5.10/1.92  %Foreground sorts:
% 5.10/1.92  
% 5.10/1.92  
% 5.10/1.92  %Background operators:
% 5.10/1.92  
% 5.10/1.92  
% 5.10/1.92  %Foreground operators:
% 5.10/1.92  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.10/1.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.10/1.92  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.10/1.92  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.10/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.10/1.92  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.10/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.10/1.92  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.10/1.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.10/1.92  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.10/1.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.10/1.92  tff('#skF_2', type, '#skF_2': $i).
% 5.10/1.92  tff('#skF_3', type, '#skF_3': $i).
% 5.10/1.92  tff('#skF_1', type, '#skF_1': $i).
% 5.10/1.92  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.10/1.92  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.10/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.10/1.92  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.10/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.10/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.10/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.10/1.92  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.10/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.10/1.92  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.10/1.92  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.10/1.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.10/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.10/1.92  
% 5.10/1.95  tff(f_181, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 5.10/1.95  tff(f_81, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.10/1.95  tff(f_115, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.10/1.95  tff(f_37, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.10/1.95  tff(f_83, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.10/1.95  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.10/1.95  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 5.10/1.95  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.10/1.95  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.10/1.95  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.10/1.95  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.10/1.95  tff(f_159, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 5.10/1.95  tff(f_113, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.10/1.95  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 5.10/1.95  tff(f_49, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 5.10/1.95  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.10/1.95  tff(c_287, plain, (![A_67, B_68, D_69]: (r2_relset_1(A_67, B_68, D_69, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.10/1.95  tff(c_298, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_287])).
% 5.10/1.95  tff(c_46, plain, (![A_26]: (k6_relat_1(A_26)=k6_partfun1(A_26))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.10/1.95  tff(c_8, plain, (![A_2]: (k2_relat_1(k6_relat_1(A_2))=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.10/1.95  tff(c_74, plain, (![A_2]: (k2_relat_1(k6_partfun1(A_2))=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 5.10/1.95  tff(c_32, plain, (![A_18]: (m1_subset_1(k6_relat_1(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.10/1.95  tff(c_73, plain, (![A_18]: (m1_subset_1(k6_partfun1(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_32])).
% 5.10/1.95  tff(c_106, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.10/1.95  tff(c_135, plain, (![A_47]: (v1_relat_1(k6_partfun1(A_47)))), inference(resolution, [status(thm)], [c_73, c_106])).
% 5.10/1.95  tff(c_2, plain, (![A_1]: (k2_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.10/1.95  tff(c_138, plain, (![A_47]: (k2_relat_1(k6_partfun1(A_47))!=k1_xboole_0 | k6_partfun1(A_47)=k1_xboole_0)), inference(resolution, [status(thm)], [c_135, c_2])).
% 5.10/1.95  tff(c_148, plain, (![A_48]: (k1_xboole_0!=A_48 | k6_partfun1(A_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_138])).
% 5.10/1.95  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.10/1.95  tff(c_154, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_148, c_56])).
% 5.10/1.95  tff(c_203, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_154])).
% 5.10/1.95  tff(c_72, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.10/1.95  tff(c_70, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.10/1.95  tff(c_66, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.10/1.95  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.10/1.95  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.10/1.95  tff(c_118, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_106])).
% 5.10/1.95  tff(c_237, plain, (![C_58, B_59, A_60]: (v5_relat_1(C_58, B_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.10/1.95  tff(c_253, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_237])).
% 5.10/1.95  tff(c_331, plain, (![B_76, A_77]: (k2_relat_1(B_76)=A_77 | ~v2_funct_2(B_76, A_77) | ~v5_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.10/1.95  tff(c_340, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_253, c_331])).
% 5.10/1.95  tff(c_352, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_340])).
% 5.10/1.95  tff(c_368, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_352])).
% 5.10/1.95  tff(c_68, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.10/1.95  tff(c_582, plain, (![C_101, B_102, A_103]: (v2_funct_2(C_101, B_102) | ~v3_funct_2(C_101, A_103, B_102) | ~v1_funct_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.10/1.95  tff(c_594, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_582])).
% 5.10/1.95  tff(c_603, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_594])).
% 5.10/1.95  tff(c_605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_368, c_603])).
% 5.10/1.95  tff(c_606, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_352])).
% 5.10/1.95  tff(c_725, plain, (![A_115, B_116, C_117]: (k2_relset_1(A_115, B_116, C_117)=k2_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.10/1.95  tff(c_737, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_725])).
% 5.10/1.95  tff(c_745, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_606, c_737])).
% 5.10/1.95  tff(c_750, plain, (![C_118, A_119, B_120]: (v2_funct_1(C_118) | ~v3_funct_2(C_118, A_119, B_120) | ~v1_funct_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.10/1.95  tff(c_762, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_750])).
% 5.10/1.95  tff(c_770, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_762])).
% 5.10/1.95  tff(c_1059, plain, (![C_156, D_157, B_158, A_159]: (k2_funct_1(C_156)=D_157 | k1_xboole_0=B_158 | k1_xboole_0=A_159 | ~v2_funct_1(C_156) | ~r2_relset_1(A_159, A_159, k1_partfun1(A_159, B_158, B_158, A_159, C_156, D_157), k6_partfun1(A_159)) | k2_relset_1(A_159, B_158, C_156)!=B_158 | ~m1_subset_1(D_157, k1_zfmisc_1(k2_zfmisc_1(B_158, A_159))) | ~v1_funct_2(D_157, B_158, A_159) | ~v1_funct_1(D_157) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_159, B_158))) | ~v1_funct_2(C_156, A_159, B_158) | ~v1_funct_1(C_156))), inference(cnfTransformation, [status(thm)], [f_159])).
% 5.10/1.95  tff(c_1065, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_1059])).
% 5.10/1.95  tff(c_1068, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_58, c_745, c_770, c_1065])).
% 5.10/1.95  tff(c_1069, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_203, c_1068])).
% 5.10/1.95  tff(c_921, plain, (![A_138, B_139]: (k2_funct_2(A_138, B_139)=k2_funct_1(B_139) | ~m1_subset_1(B_139, k1_zfmisc_1(k2_zfmisc_1(A_138, A_138))) | ~v3_funct_2(B_139, A_138, A_138) | ~v1_funct_2(B_139, A_138, A_138) | ~v1_funct_1(B_139))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.10/1.95  tff(c_933, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_921])).
% 5.10/1.95  tff(c_941, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_933])).
% 5.10/1.95  tff(c_54, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.10/1.95  tff(c_946, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_941, c_54])).
% 5.10/1.95  tff(c_1070, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1069, c_946])).
% 5.10/1.95  tff(c_1074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_298, c_1070])).
% 5.10/1.95  tff(c_1076, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_154])).
% 5.10/1.95  tff(c_117, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_106])).
% 5.10/1.95  tff(c_125, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_117, c_2])).
% 5.10/1.95  tff(c_146, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_125])).
% 5.10/1.95  tff(c_1079, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1076, c_146])).
% 5.10/1.95  tff(c_1087, plain, (![C_161, B_162, A_163]: (v5_relat_1(C_161, B_162) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_163, B_162))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.10/1.95  tff(c_1098, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_1087])).
% 5.10/1.95  tff(c_1244, plain, (![B_178, A_179]: (k2_relat_1(B_178)=A_179 | ~v2_funct_2(B_178, A_179) | ~v5_relat_1(B_178, A_179) | ~v1_relat_1(B_178))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.10/1.95  tff(c_1256, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1098, c_1244])).
% 5.10/1.95  tff(c_1269, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_1256])).
% 5.10/1.95  tff(c_1270, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1079, c_1269])).
% 5.10/1.95  tff(c_60, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_181])).
% 5.10/1.95  tff(c_1418, plain, (![C_200, B_201, A_202]: (v2_funct_2(C_200, B_201) | ~v3_funct_2(C_200, A_202, B_201) | ~v1_funct_1(C_200) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_202, B_201))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.10/1.95  tff(c_1427, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_1418])).
% 5.10/1.95  tff(c_1436, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_1427])).
% 5.10/1.95  tff(c_1438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1270, c_1436])).
% 5.10/1.95  tff(c_1439, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_125])).
% 5.10/1.95  tff(c_143, plain, (![A_47]: (k1_xboole_0!=A_47 | k6_partfun1(A_47)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_138])).
% 5.10/1.95  tff(c_1454, plain, (![A_203]: (A_203!='#skF_3' | k6_partfun1(A_203)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1439, c_1439, c_143])).
% 5.10/1.95  tff(c_1460, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_3') | '#skF_3'!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1454, c_56])).
% 5.10/1.95  tff(c_1498, plain, ('#skF_3'!='#skF_1'), inference(splitLeft, [status(thm)], [c_1460])).
% 5.10/1.95  tff(c_1440, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_125])).
% 5.10/1.95  tff(c_1447, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1439, c_1440])).
% 5.10/1.95  tff(c_1533, plain, (![C_212, B_213, A_214]: (v5_relat_1(C_212, B_213) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_214, B_213))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.10/1.95  tff(c_1544, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_1533])).
% 5.10/1.95  tff(c_1638, plain, (![B_228, A_229]: (k2_relat_1(B_228)=A_229 | ~v2_funct_2(B_228, A_229) | ~v5_relat_1(B_228, A_229) | ~v1_relat_1(B_228))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.10/1.95  tff(c_1650, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1544, c_1638])).
% 5.10/1.95  tff(c_1662, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_1447, c_1650])).
% 5.10/1.95  tff(c_1663, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1498, c_1662])).
% 5.10/1.95  tff(c_1811, plain, (![C_246, B_247, A_248]: (v2_funct_2(C_246, B_247) | ~v3_funct_2(C_246, A_248, B_247) | ~v1_funct_1(C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_248, B_247))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.10/1.95  tff(c_1820, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_1811])).
% 5.10/1.95  tff(c_1831, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_1820])).
% 5.10/1.95  tff(c_1833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1663, c_1831])).
% 5.10/1.95  tff(c_1835, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1460])).
% 5.10/1.95  tff(c_6, plain, (![A_2]: (k1_relat_1(k6_relat_1(A_2))=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.10/1.95  tff(c_75, plain, (![A_2]: (k1_relat_1(k6_partfun1(A_2))=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6])).
% 5.10/1.95  tff(c_1468, plain, (![A_203]: (k1_relat_1('#skF_3')=A_203 | A_203!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1454, c_75])).
% 5.10/1.95  tff(c_2253, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1835, c_1835, c_1468])).
% 5.10/1.95  tff(c_1840, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1835, c_1439])).
% 5.10/1.95  tff(c_133, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_118, c_2])).
% 5.10/1.95  tff(c_1861, plain, (k2_relat_1('#skF_2')!='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1840, c_1840, c_133])).
% 5.10/1.95  tff(c_1862, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1861])).
% 5.10/1.95  tff(c_1972, plain, (![C_258, B_259, A_260]: (v5_relat_1(C_258, B_259) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_260, B_259))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.10/1.95  tff(c_1984, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_1972])).
% 5.10/1.95  tff(c_2042, plain, (![B_268, A_269]: (k2_relat_1(B_268)=A_269 | ~v2_funct_2(B_268, A_269) | ~v5_relat_1(B_268, A_269) | ~v1_relat_1(B_268))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.10/1.95  tff(c_2051, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1984, c_2042])).
% 5.10/1.95  tff(c_2060, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_2051])).
% 5.10/1.95  tff(c_2061, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1862, c_2060])).
% 5.10/1.95  tff(c_2171, plain, (![C_286, B_287, A_288]: (v2_funct_2(C_286, B_287) | ~v3_funct_2(C_286, A_288, B_287) | ~v1_funct_1(C_286) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_288, B_287))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.10/1.95  tff(c_2180, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_2171])).
% 5.10/1.95  tff(c_2188, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_2180])).
% 5.10/1.95  tff(c_2190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2061, c_2188])).
% 5.10/1.95  tff(c_2191, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_1861])).
% 5.10/1.95  tff(c_4, plain, (![A_1]: (k1_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.10/1.95  tff(c_134, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_118, c_4])).
% 5.10/1.95  tff(c_1479, plain, (k1_relat_1('#skF_2')!='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1439, c_1439, c_134])).
% 5.10/1.95  tff(c_1480, plain, (k1_relat_1('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_1479])).
% 5.10/1.95  tff(c_1837, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1835, c_1480])).
% 5.10/1.95  tff(c_2193, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2191, c_1837])).
% 5.10/1.95  tff(c_2256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2253, c_2193])).
% 5.10/1.95  tff(c_2257, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1479])).
% 5.10/1.95  tff(c_2389, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_3'), '#skF_3') | '#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2257, c_1460])).
% 5.10/1.95  tff(c_2390, plain, ('#skF_3'!='#skF_1'), inference(splitLeft, [status(thm)], [c_2389])).
% 5.10/1.95  tff(c_2301, plain, (![C_296, B_297, A_298]: (v5_relat_1(C_296, B_297) | ~m1_subset_1(C_296, k1_zfmisc_1(k2_zfmisc_1(A_298, B_297))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.10/1.95  tff(c_2309, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_2301])).
% 5.10/1.95  tff(c_2448, plain, (![B_319, A_320]: (k2_relat_1(B_319)=A_320 | ~v2_funct_2(B_319, A_320) | ~v5_relat_1(B_319, A_320) | ~v1_relat_1(B_319))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.10/1.95  tff(c_2457, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2309, c_2448])).
% 5.10/1.95  tff(c_2466, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_1447, c_2457])).
% 5.10/1.95  tff(c_2467, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2390, c_2466])).
% 5.10/1.95  tff(c_2521, plain, (![C_328, B_329, A_330]: (v2_funct_2(C_328, B_329) | ~v3_funct_2(C_328, A_330, B_329) | ~v1_funct_1(C_328) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_330, B_329))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.10/1.95  tff(c_2530, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2521])).
% 5.10/1.95  tff(c_2538, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2530])).
% 5.10/1.95  tff(c_2540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2467, c_2538])).
% 5.10/1.95  tff(c_2542, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_2389])).
% 5.10/1.95  tff(c_1465, plain, (![A_203]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_203, A_203))) | A_203!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1454, c_73])).
% 5.10/1.95  tff(c_2544, plain, (![A_203]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_203, A_203))) | A_203!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2542, c_2542, c_1465])).
% 5.10/1.95  tff(c_2743, plain, (![A_343, B_344, D_345]: (r2_relset_1(A_343, B_344, D_345, D_345) | ~m1_subset_1(D_345, k1_zfmisc_1(k2_zfmisc_1(A_343, B_344))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.10/1.95  tff(c_2758, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2544, c_2743])).
% 5.10/1.95  tff(c_2560, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2542, c_62])).
% 5.10/1.95  tff(c_2561, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2542, c_60])).
% 5.10/1.95  tff(c_2562, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2542, c_64])).
% 5.10/1.95  tff(c_2558, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2542, c_117])).
% 5.10/1.95  tff(c_2832, plain, (![C_358, A_359, B_360]: (v2_funct_1(C_358) | ~v3_funct_2(C_358, A_359, B_360) | ~v1_funct_1(C_358) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_359, B_360))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.10/1.95  tff(c_2835, plain, (![A_203]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_203, A_203) | ~v1_funct_1('#skF_1') | A_203!='#skF_1')), inference(resolution, [status(thm)], [c_2544, c_2832])).
% 5.10/1.95  tff(c_2841, plain, (![A_203]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_203, A_203) | A_203!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2562, c_2835])).
% 5.10/1.95  tff(c_2856, plain, (~v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_2841])).
% 5.10/1.95  tff(c_2858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2856, c_2561])).
% 5.10/1.95  tff(c_2859, plain, (v2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_2841])).
% 5.10/1.95  tff(c_2258, plain, (k1_relat_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1479])).
% 5.10/1.95  tff(c_2284, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2257, c_2258])).
% 5.10/1.95  tff(c_2552, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2542, c_2542, c_2284])).
% 5.10/1.95  tff(c_16, plain, (![A_4]: (k2_relat_1(k2_funct_1(A_4))=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.10/1.95  tff(c_2359, plain, (![A_304]: (v1_relat_1(k2_funct_1(A_304)) | ~v2_funct_1(A_304) | ~v1_funct_1(A_304) | ~v1_relat_1(A_304))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.10/1.95  tff(c_1441, plain, (![A_1]: (k2_relat_1(A_1)!='#skF_3' | A_1='#skF_3' | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1439, c_1439, c_2])).
% 5.10/1.95  tff(c_2366, plain, (![A_304]: (k2_relat_1(k2_funct_1(A_304))!='#skF_3' | k2_funct_1(A_304)='#skF_3' | ~v2_funct_1(A_304) | ~v1_funct_1(A_304) | ~v1_relat_1(A_304))), inference(resolution, [status(thm)], [c_2359, c_1441])).
% 5.10/1.95  tff(c_2828, plain, (![A_357]: (k2_relat_1(k2_funct_1(A_357))!='#skF_1' | k2_funct_1(A_357)='#skF_1' | ~v2_funct_1(A_357) | ~v1_funct_1(A_357) | ~v1_relat_1(A_357))), inference(demodulation, [status(thm), theory('equality')], [c_2542, c_2542, c_2366])).
% 5.10/1.95  tff(c_2897, plain, (![A_370]: (k1_relat_1(A_370)!='#skF_1' | k2_funct_1(A_370)='#skF_1' | ~v2_funct_1(A_370) | ~v1_funct_1(A_370) | ~v1_relat_1(A_370) | ~v2_funct_1(A_370) | ~v1_funct_1(A_370) | ~v1_relat_1(A_370))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2828])).
% 5.10/1.95  tff(c_2899, plain, (k1_relat_1('#skF_1')!='#skF_1' | k2_funct_1('#skF_1')='#skF_1' | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2859, c_2897])).
% 5.10/1.95  tff(c_2904, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2562, c_2859, c_2552, c_2899])).
% 5.10/1.95  tff(c_2954, plain, (![A_372, B_373]: (k2_funct_2(A_372, B_373)=k2_funct_1(B_373) | ~m1_subset_1(B_373, k1_zfmisc_1(k2_zfmisc_1(A_372, A_372))) | ~v3_funct_2(B_373, A_372, A_372) | ~v1_funct_2(B_373, A_372, A_372) | ~v1_funct_1(B_373))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.10/1.95  tff(c_2957, plain, (![A_203]: (k2_funct_2(A_203, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_203, A_203) | ~v1_funct_2('#skF_1', A_203, A_203) | ~v1_funct_1('#skF_1') | A_203!='#skF_1')), inference(resolution, [status(thm)], [c_2544, c_2954])).
% 5.10/1.95  tff(c_2966, plain, (![A_374]: (k2_funct_2(A_374, '#skF_1')='#skF_1' | ~v3_funct_2('#skF_1', A_374, A_374) | ~v1_funct_2('#skF_1', A_374, A_374) | A_374!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2562, c_2904, c_2957])).
% 5.10/1.95  tff(c_2969, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2561, c_2966])).
% 5.10/1.95  tff(c_2972, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2560, c_2969])).
% 5.10/1.95  tff(c_2261, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2257, c_54])).
% 5.10/1.95  tff(c_2551, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2542, c_2542, c_2261])).
% 5.10/1.95  tff(c_2973, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2972, c_2551])).
% 5.10/1.95  tff(c_2976, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2758, c_2973])).
% 5.10/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.95  
% 5.10/1.95  Inference rules
% 5.10/1.95  ----------------------
% 5.10/1.95  #Ref     : 7
% 5.10/1.95  #Sup     : 590
% 5.10/1.95  #Fact    : 0
% 5.10/1.95  #Define  : 0
% 5.10/1.95  #Split   : 24
% 5.10/1.95  #Chain   : 0
% 5.10/1.95  #Close   : 0
% 5.10/1.95  
% 5.10/1.95  Ordering : KBO
% 5.10/1.95  
% 5.10/1.95  Simplification rules
% 5.10/1.95  ----------------------
% 5.10/1.95  #Subsume      : 92
% 5.10/1.95  #Demod        : 552
% 5.10/1.95  #Tautology    : 303
% 5.10/1.95  #SimpNegUnit  : 21
% 5.10/1.95  #BackRed      : 64
% 5.10/1.95  
% 5.10/1.95  #Partial instantiations: 0
% 5.10/1.95  #Strategies tried      : 1
% 5.10/1.95  
% 5.10/1.95  Timing (in seconds)
% 5.10/1.95  ----------------------
% 5.10/1.95  Preprocessing        : 0.38
% 5.10/1.95  Parsing              : 0.20
% 5.10/1.95  CNF conversion       : 0.03
% 5.10/1.95  Main loop            : 0.77
% 5.10/1.95  Inferencing          : 0.29
% 5.10/1.95  Reduction            : 0.27
% 5.10/1.95  Demodulation         : 0.19
% 5.10/1.95  BG Simplification    : 0.03
% 5.10/1.95  Subsumption          : 0.11
% 5.10/1.95  Abstraction          : 0.03
% 5.10/1.95  MUC search           : 0.00
% 5.10/1.95  Cooper               : 0.00
% 5.10/1.95  Total                : 1.22
% 5.10/1.95  Index Insertion      : 0.00
% 5.10/1.95  Index Deletion       : 0.00
% 5.10/1.95  Index Matching       : 0.00
% 5.10/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
