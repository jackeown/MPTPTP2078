%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0984+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:11 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  206 (3446 expanded)
%              Number of leaves         :   29 (1016 expanded)
%              Depth                    :   16
%              Number of atoms          :  374 (15288 expanded)
%              Number of equality atoms :  137 (6026 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_81,axiom,(
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

tff(c_26,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_389,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_46,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_51,plain,(
    ! [C_23,A_24,B_25] :
      ( v1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_59,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_51])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_51])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_45,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_36,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_79,plain,(
    ! [A_30,B_31,C_32] :
      ( k1_relset_1(A_30,B_31,C_32) = k1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_87,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_79])).

tff(c_111,plain,(
    ! [B_42,A_43,C_44] :
      ( k1_xboole_0 = B_42
      | k1_relset_1(A_43,B_42,C_44) = A_43
      | ~ v1_funct_2(C_44,A_43,B_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_43,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_117,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_111])).

tff(c_123,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_87,c_117])).

tff(c_124,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_123])).

tff(c_30,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_60,plain,(
    ! [A_26,B_27,C_28] :
      ( k2_relset_1(A_26,B_27,C_28) = k2_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_63,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_60])).

tff(c_68,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_63])).

tff(c_146,plain,(
    ! [F_53,C_51,E_54,D_49,B_50,A_52] :
      ( k1_partfun1(A_52,B_50,C_51,D_49,E_54,F_53) = k5_relat_1(E_54,F_53)
      | ~ m1_subset_1(F_53,k1_zfmisc_1(k2_zfmisc_1(C_51,D_49)))
      | ~ v1_funct_1(F_53)
      | ~ m1_subset_1(E_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_50)))
      | ~ v1_funct_1(E_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_150,plain,(
    ! [A_52,B_50,E_54] :
      ( k1_partfun1(A_52,B_50,'#skF_2','#skF_3',E_54,'#skF_5') = k5_relat_1(E_54,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_50)))
      | ~ v1_funct_1(E_54) ) ),
    inference(resolution,[status(thm)],[c_34,c_146])).

tff(c_178,plain,(
    ! [A_58,B_59,E_60] :
      ( k1_partfun1(A_58,B_59,'#skF_2','#skF_3',E_60,'#skF_5') = k5_relat_1(E_60,'#skF_5')
      | ~ m1_subset_1(E_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_funct_1(E_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_150])).

tff(c_181,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_178])).

tff(c_187,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_181])).

tff(c_32,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_191,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_32])).

tff(c_24,plain,(
    ! [B_21,A_19] :
      ( v2_funct_1(B_21)
      | k2_relat_1(B_21) != k1_relat_1(A_19)
      | ~ v2_funct_1(k5_relat_1(B_21,A_19))
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_198,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_191,c_24])).

tff(c_204,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_38,c_58,c_44,c_124,c_68,c_198])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_204])).

tff(c_207,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_213,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_221,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_213])).

tff(c_220,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_213])).

tff(c_223,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_relset_1(A_65,B_66,C_67) = k1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_231,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_223])).

tff(c_261,plain,(
    ! [B_77,A_78,C_79] :
      ( k1_xboole_0 = B_77
      | k1_relset_1(A_78,B_77,C_79) = A_78
      | ~ v1_funct_2(C_79,A_78,B_77)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_267,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_261])).

tff(c_273,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_231,c_267])).

tff(c_274,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_273])).

tff(c_240,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_243,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_240])).

tff(c_248,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_243])).

tff(c_309,plain,(
    ! [C_89,F_91,B_88,E_92,D_87,A_90] :
      ( k1_partfun1(A_90,B_88,C_89,D_87,E_92,F_91) = k5_relat_1(E_92,F_91)
      | ~ m1_subset_1(F_91,k1_zfmisc_1(k2_zfmisc_1(C_89,D_87)))
      | ~ v1_funct_1(F_91)
      | ~ m1_subset_1(E_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_88)))
      | ~ v1_funct_1(E_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_313,plain,(
    ! [A_90,B_88,E_92] :
      ( k1_partfun1(A_90,B_88,'#skF_2','#skF_3',E_92,'#skF_5') = k5_relat_1(E_92,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_88)))
      | ~ v1_funct_1(E_92) ) ),
    inference(resolution,[status(thm)],[c_34,c_309])).

tff(c_341,plain,(
    ! [A_96,B_97,E_98] :
      ( k1_partfun1(A_96,B_97,'#skF_2','#skF_3',E_98,'#skF_5') = k5_relat_1(E_98,'#skF_5')
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_1(E_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_313])).

tff(c_344,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_341])).

tff(c_350,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_344])).

tff(c_354,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_32])).

tff(c_22,plain,(
    ! [A_19,B_21] :
      ( v2_funct_1(A_19)
      | k2_relat_1(B_21) != k1_relat_1(A_19)
      | ~ v2_funct_1(k5_relat_1(B_21,A_19))
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_364,plain,
    ( v2_funct_1('#skF_5')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_354,c_22])).

tff(c_370,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_38,c_220,c_44,c_274,c_248,c_364])).

tff(c_372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_370])).

tff(c_374,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_373,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_379,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_373])).

tff(c_396,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_34])).

tff(c_399,plain,(
    ! [C_99,A_100,B_101] :
      ( v1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_407,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_396,c_399])).

tff(c_397,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_40])).

tff(c_406,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_397,c_399])).

tff(c_42,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_384,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_42])).

tff(c_6,plain,(
    ! [C_6,A_4] :
      ( k1_xboole_0 = C_6
      | ~ v1_funct_2(C_6,A_4,k1_xboole_0)
      | k1_xboole_0 = A_4
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_438,plain,(
    ! [C_109,A_110] :
      ( C_109 = '#skF_3'
      | ~ v1_funct_2(C_109,A_110,'#skF_3')
      | A_110 = '#skF_3'
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_374,c_374,c_374,c_6])).

tff(c_441,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_397,c_438])).

tff(c_447,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_441])).

tff(c_456,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_447])).

tff(c_390,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_36])).

tff(c_466,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_456,c_390])).

tff(c_410,plain,(
    ! [A_103,B_104,C_105] :
      ( k1_relset_1(A_103,B_104,C_105) = k1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_418,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_396,c_410])).

tff(c_459,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_456,c_418])).

tff(c_464,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_456,c_396])).

tff(c_469,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_374])).

tff(c_12,plain,(
    ! [B_5,C_6] :
      ( k1_relset_1(k1_xboole_0,B_5,C_6) = k1_xboole_0
      | ~ v1_funct_2(C_6,k1_xboole_0,B_5)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_562,plain,(
    ! [B_116,C_117] :
      ( k1_relset_1('#skF_1',B_116,C_117) = '#skF_1'
      | ~ v1_funct_2(C_117,'#skF_1',B_116)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_116))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_469,c_469,c_469,c_12])).

tff(c_565,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_464,c_562])).

tff(c_571,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_459,c_565])).

tff(c_391,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_379,c_30])).

tff(c_427,plain,(
    ! [A_106,B_107,C_108] :
      ( k2_relset_1(A_106,B_107,C_108) = k2_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_430,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_397,c_427])).

tff(c_435,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_430])).

tff(c_457,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_435])).

tff(c_463,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_397])).

tff(c_625,plain,(
    ! [B_129,E_133,C_130,A_131,F_132,D_128] :
      ( k1_partfun1(A_131,B_129,C_130,D_128,E_133,F_132) = k5_relat_1(E_133,F_132)
      | ~ m1_subset_1(F_132,k1_zfmisc_1(k2_zfmisc_1(C_130,D_128)))
      | ~ v1_funct_1(F_132)
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_129)))
      | ~ v1_funct_1(E_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_627,plain,(
    ! [A_131,B_129,E_133] :
      ( k1_partfun1(A_131,B_129,'#skF_1','#skF_1',E_133,'#skF_5') = k5_relat_1(E_133,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_129)))
      | ~ v1_funct_1(E_133) ) ),
    inference(resolution,[status(thm)],[c_464,c_625])).

tff(c_636,plain,(
    ! [A_134,B_135,E_136] :
      ( k1_partfun1(A_134,B_135,'#skF_1','#skF_1',E_136,'#skF_5') = k5_relat_1(E_136,'#skF_5')
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_1(E_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_627])).

tff(c_642,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_463,c_636])).

tff(c_648,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_642])).

tff(c_398,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_379,c_32])).

tff(c_462,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_456,c_456,c_398])).

tff(c_674,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_462])).

tff(c_681,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_674,c_24])).

tff(c_687,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_38,c_406,c_44,c_571,c_457,c_681])).

tff(c_689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_687])).

tff(c_690,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_701,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_690,c_390])).

tff(c_694,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_690,c_418])).

tff(c_699,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_690,c_396])).

tff(c_704,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_374])).

tff(c_718,plain,(
    ! [B_5,C_6] :
      ( k1_relset_1('#skF_4',B_5,C_6) = '#skF_4'
      | ~ v1_funct_2(C_6,'#skF_4',B_5)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_5))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_704,c_704,c_704,c_12])).

tff(c_757,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_699,c_718])).

tff(c_769,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_701,c_694,c_757])).

tff(c_692,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_435])).

tff(c_698,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_397])).

tff(c_849,plain,(
    ! [E_162,C_159,D_157,A_160,F_161,B_158] :
      ( k1_partfun1(A_160,B_158,C_159,D_157,E_162,F_161) = k5_relat_1(E_162,F_161)
      | ~ m1_subset_1(F_161,k1_zfmisc_1(k2_zfmisc_1(C_159,D_157)))
      | ~ v1_funct_1(F_161)
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_158)))
      | ~ v1_funct_1(E_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_851,plain,(
    ! [A_160,B_158,E_162] :
      ( k1_partfun1(A_160,B_158,'#skF_4','#skF_4',E_162,'#skF_5') = k5_relat_1(E_162,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_158)))
      | ~ v1_funct_1(E_162) ) ),
    inference(resolution,[status(thm)],[c_699,c_849])).

tff(c_860,plain,(
    ! [A_163,B_164,E_165] :
      ( k1_partfun1(A_163,B_164,'#skF_4','#skF_4',E_165,'#skF_5') = k5_relat_1(E_165,'#skF_5')
      | ~ m1_subset_1(E_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164)))
      | ~ v1_funct_1(E_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_851])).

tff(c_866,plain,
    ( k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_698,c_860])).

tff(c_872,plain,(
    k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_866])).

tff(c_697,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_690,c_690,c_398])).

tff(c_877,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_872,c_697])).

tff(c_884,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_877,c_24])).

tff(c_890,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_38,c_406,c_44,c_769,c_692,c_884])).

tff(c_892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_890])).

tff(c_893,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_902,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_34])).

tff(c_903,plain,(
    ! [C_166,A_167,B_168] :
      ( v1_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_910,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_902,c_903])).

tff(c_901,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_40])).

tff(c_911,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_901,c_903])).

tff(c_951,plain,(
    ! [C_176,A_177] :
      ( C_176 = '#skF_3'
      | ~ v1_funct_2(C_176,A_177,'#skF_3')
      | A_177 = '#skF_3'
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_177,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_374,c_374,c_374,c_6])).

tff(c_957,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_901,c_951])).

tff(c_964,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_957])).

tff(c_965,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_964])).

tff(c_895,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_36])).

tff(c_977,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_965,c_895])).

tff(c_933,plain,(
    ! [A_173,B_174,C_175] :
      ( k1_relset_1(A_173,B_174,C_175) = k1_relat_1(C_175)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_940,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_902,c_933])).

tff(c_968,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_965,c_940])).

tff(c_973,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_965,c_902])).

tff(c_979,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_374])).

tff(c_1055,plain,(
    ! [B_180,C_181] :
      ( k1_relset_1('#skF_1',B_180,C_181) = '#skF_1'
      | ~ v1_funct_2(C_181,'#skF_1',B_180)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_180))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_979,c_979,c_979,c_12])).

tff(c_1058,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_973,c_1055])).

tff(c_1064,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_977,c_968,c_1058])).

tff(c_896,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_379,c_30])).

tff(c_913,plain,(
    ! [A_169,B_170,C_171] :
      ( k2_relset_1(A_169,B_170,C_171) = k2_relat_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_919,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_901,c_913])).

tff(c_922,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_896,c_919])).

tff(c_971,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_922])).

tff(c_974,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_901])).

tff(c_1136,plain,(
    ! [F_199,D_195,E_200,B_196,C_197,A_198] :
      ( k1_partfun1(A_198,B_196,C_197,D_195,E_200,F_199) = k5_relat_1(E_200,F_199)
      | ~ m1_subset_1(F_199,k1_zfmisc_1(k2_zfmisc_1(C_197,D_195)))
      | ~ v1_funct_1(F_199)
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_196)))
      | ~ v1_funct_1(E_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1138,plain,(
    ! [A_198,B_196,E_200] :
      ( k1_partfun1(A_198,B_196,'#skF_1','#skF_1',E_200,'#skF_5') = k5_relat_1(E_200,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_196)))
      | ~ v1_funct_1(E_200) ) ),
    inference(resolution,[status(thm)],[c_973,c_1136])).

tff(c_1147,plain,(
    ! [A_201,B_202,E_203] :
      ( k1_partfun1(A_201,B_202,'#skF_1','#skF_1',E_203,'#skF_5') = k5_relat_1(E_203,'#skF_5')
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202)))
      | ~ v1_funct_1(E_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1138])).

tff(c_1153,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_974,c_1147])).

tff(c_1159,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1153])).

tff(c_912,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_379,c_32])).

tff(c_972,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_965,c_965,c_912])).

tff(c_1164,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1159,c_972])).

tff(c_1171,plain,
    ( v2_funct_1('#skF_5')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1164,c_22])).

tff(c_1177,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_38,c_911,c_44,c_1064,c_971,c_1171])).

tff(c_1179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_893,c_1177])).

tff(c_1180,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_964])).

tff(c_1193,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_1180,c_895])).

tff(c_1184,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_1180,c_940])).

tff(c_1189,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_1180,c_902])).

tff(c_1195,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_374])).

tff(c_1246,plain,(
    ! [B_206,C_207] :
      ( k1_relset_1('#skF_4',B_206,C_207) = '#skF_4'
      | ~ v1_funct_2(C_207,'#skF_4',B_206)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_206))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1195,c_1195,c_1195,c_1195,c_12])).

tff(c_1249,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1189,c_1246])).

tff(c_1252,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1193,c_1184,c_1249])).

tff(c_1187,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_922])).

tff(c_1190,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_901])).

tff(c_1341,plain,(
    ! [C_225,E_228,D_223,F_227,B_224,A_226] :
      ( k1_partfun1(A_226,B_224,C_225,D_223,E_228,F_227) = k5_relat_1(E_228,F_227)
      | ~ m1_subset_1(F_227,k1_zfmisc_1(k2_zfmisc_1(C_225,D_223)))
      | ~ v1_funct_1(F_227)
      | ~ m1_subset_1(E_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_224)))
      | ~ v1_funct_1(E_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1345,plain,(
    ! [A_226,B_224,E_228] :
      ( k1_partfun1(A_226,B_224,'#skF_4','#skF_4',E_228,'#skF_5') = k5_relat_1(E_228,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_224)))
      | ~ v1_funct_1(E_228) ) ),
    inference(resolution,[status(thm)],[c_1189,c_1341])).

tff(c_1373,plain,(
    ! [A_232,B_233,E_234] :
      ( k1_partfun1(A_232,B_233,'#skF_4','#skF_4',E_234,'#skF_5') = k5_relat_1(E_234,'#skF_5')
      | ~ m1_subset_1(E_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233)))
      | ~ v1_funct_1(E_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1345])).

tff(c_1376,plain,
    ( k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1190,c_1373])).

tff(c_1382,plain,(
    k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1376])).

tff(c_1188,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_1180,c_1180,c_912])).

tff(c_1386,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1382,c_1188])).

tff(c_1396,plain,
    ( v2_funct_1('#skF_5')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1386,c_22])).

tff(c_1402,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_38,c_911,c_44,c_1252,c_1187,c_1396])).

tff(c_1404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_893,c_1402])).

%------------------------------------------------------------------------------
