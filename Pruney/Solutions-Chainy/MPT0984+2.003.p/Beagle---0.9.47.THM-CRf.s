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
% DateTime   : Thu Dec  3 10:12:25 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  217 (3483 expanded)
%              Number of leaves         :   30 (1028 expanded)
%              Depth                    :   16
%              Number of atoms          :  398 (15361 expanded)
%              Number of equality atoms :  138 (6027 expanded)
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

tff(f_114,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

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

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_77,axiom,(
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

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_51,axiom,(
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

tff(c_28,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_381,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_49,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_54,plain,(
    ! [B_27,A_28] :
      ( v1_relat_1(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_28))
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_54])).

tff(c_63,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_57])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_60,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_54])).

tff(c_66,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_60])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_30,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_47,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_38,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_67,plain,(
    ! [A_29,B_30,C_31] :
      ( k1_relset_1(A_29,B_30,C_31) = k1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_74,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_67])).

tff(c_106,plain,(
    ! [B_42,A_43,C_44] :
      ( k1_xboole_0 = B_42
      | k1_relset_1(A_43,B_42,C_44) = A_43
      | ~ v1_funct_2(C_44,A_43,B_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_43,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_109,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_106])).

tff(c_115,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_74,c_109])).

tff(c_116,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_115])).

tff(c_32,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_84,plain,(
    ! [A_32,B_33,C_34] :
      ( k2_relset_1(A_32,B_33,C_34) = k2_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_90,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_84])).

tff(c_93,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_90])).

tff(c_155,plain,(
    ! [D_56,E_54,B_57,A_52,F_55,C_53] :
      ( k1_partfun1(A_52,B_57,C_53,D_56,E_54,F_55) = k5_relat_1(E_54,F_55)
      | ~ m1_subset_1(F_55,k1_zfmisc_1(k2_zfmisc_1(C_53,D_56)))
      | ~ v1_funct_1(F_55)
      | ~ m1_subset_1(E_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_57)))
      | ~ v1_funct_1(E_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_157,plain,(
    ! [A_52,B_57,E_54] :
      ( k1_partfun1(A_52,B_57,'#skF_2','#skF_3',E_54,'#skF_5') = k5_relat_1(E_54,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_57)))
      | ~ v1_funct_1(E_54) ) ),
    inference(resolution,[status(thm)],[c_36,c_155])).

tff(c_166,plain,(
    ! [A_58,B_59,E_60] :
      ( k1_partfun1(A_58,B_59,'#skF_2','#skF_3',E_60,'#skF_5') = k5_relat_1(E_60,'#skF_5')
      | ~ m1_subset_1(E_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_funct_1(E_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_157])).

tff(c_172,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_166])).

tff(c_178,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_172])).

tff(c_34,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_183,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_34])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( v2_funct_1(B_8)
      | k2_relat_1(B_8) != k1_relat_1(A_6)
      | ~ v2_funct_1(k5_relat_1(B_8,A_6))
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_190,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_183,c_8])).

tff(c_196,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_40,c_66,c_46,c_116,c_93,c_190])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_196])).

tff(c_199,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_205,plain,(
    ! [B_61,A_62] :
      ( v1_relat_1(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62))
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_211,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_205])).

tff(c_217,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_211])).

tff(c_208,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_205])).

tff(c_214,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_208])).

tff(c_219,plain,(
    ! [A_64,B_65,C_66] :
      ( k1_relset_1(A_64,B_65,C_66) = k1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_227,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_219])).

tff(c_269,plain,(
    ! [B_79,A_80,C_81] :
      ( k1_xboole_0 = B_79
      | k1_relset_1(A_80,B_79,C_81) = A_80
      | ~ v1_funct_2(C_81,A_80,B_79)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_275,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_269])).

tff(c_281,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_227,c_275])).

tff(c_282,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_281])).

tff(c_236,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_relset_1(A_67,B_68,C_69) = k2_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_239,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_236])).

tff(c_244,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_239])).

tff(c_304,plain,(
    ! [E_88,F_89,B_91,C_87,D_90,A_86] :
      ( k1_partfun1(A_86,B_91,C_87,D_90,E_88,F_89) = k5_relat_1(E_88,F_89)
      | ~ m1_subset_1(F_89,k1_zfmisc_1(k2_zfmisc_1(C_87,D_90)))
      | ~ v1_funct_1(F_89)
      | ~ m1_subset_1(E_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_91)))
      | ~ v1_funct_1(E_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_308,plain,(
    ! [A_86,B_91,E_88] :
      ( k1_partfun1(A_86,B_91,'#skF_2','#skF_3',E_88,'#skF_5') = k5_relat_1(E_88,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_91)))
      | ~ v1_funct_1(E_88) ) ),
    inference(resolution,[status(thm)],[c_36,c_304])).

tff(c_336,plain,(
    ! [A_95,B_96,E_97] :
      ( k1_partfun1(A_95,B_96,'#skF_2','#skF_3',E_97,'#skF_5') = k5_relat_1(E_97,'#skF_5')
      | ~ m1_subset_1(E_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_1(E_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_308])).

tff(c_339,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_336])).

tff(c_345,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_339])).

tff(c_349,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_34])).

tff(c_6,plain,(
    ! [A_6,B_8] :
      ( v2_funct_1(A_6)
      | k2_relat_1(B_8) != k1_relat_1(A_6)
      | ~ v2_funct_1(k5_relat_1(B_8,A_6))
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_356,plain,
    ( v2_funct_1('#skF_5')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_349,c_6])).

tff(c_362,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_40,c_214,c_46,c_282,c_244,c_356])).

tff(c_364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_362])).

tff(c_366,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_365,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_371,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_365])).

tff(c_390,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_36])).

tff(c_392,plain,(
    ! [B_100,A_101] :
      ( v1_relat_1(B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_101))
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_395,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_390,c_392])).

tff(c_401,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_395])).

tff(c_389,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_42])).

tff(c_398,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_389,c_392])).

tff(c_404,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_398])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_376,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_44])).

tff(c_16,plain,(
    ! [C_17,A_15] :
      ( k1_xboole_0 = C_17
      | ~ v1_funct_2(C_17,A_15,k1_xboole_0)
      | k1_xboole_0 = A_15
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_443,plain,(
    ! [C_109,A_110] :
      ( C_109 = '#skF_3'
      | ~ v1_funct_2(C_109,A_110,'#skF_3')
      | A_110 = '#skF_3'
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_366,c_366,c_366,c_16])).

tff(c_449,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_389,c_443])).

tff(c_456,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_449])).

tff(c_457,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_456])).

tff(c_382,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_38])).

tff(c_469,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_457,c_382])).

tff(c_465,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_457,c_390])).

tff(c_471,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_366])).

tff(c_22,plain,(
    ! [B_16,C_17] :
      ( k1_relset_1(k1_xboole_0,B_16,C_17) = k1_xboole_0
      | ~ v1_funct_2(C_17,k1_xboole_0,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_488,plain,(
    ! [B_16,C_17] :
      ( k1_relset_1('#skF_1',B_16,C_17) = '#skF_1'
      | ~ v1_funct_2(C_17,'#skF_1',B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_16))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_471,c_471,c_471,c_22])).

tff(c_521,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_465,c_488])).

tff(c_533,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_521])).

tff(c_423,plain,(
    ! [A_105,B_106,C_107] :
      ( k1_relset_1(A_105,B_106,C_107) = k1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_430,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_390,c_423])).

tff(c_461,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_457,c_430])).

tff(c_547,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_461])).

tff(c_384,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_371,c_32])).

tff(c_405,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_relset_1(A_102,B_103,C_104) = k2_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_411,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_389,c_405])).

tff(c_414,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_411])).

tff(c_463,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_414])).

tff(c_466,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_389])).

tff(c_624,plain,(
    ! [B_133,E_130,F_131,A_128,D_132,C_129] :
      ( k1_partfun1(A_128,B_133,C_129,D_132,E_130,F_131) = k5_relat_1(E_130,F_131)
      | ~ m1_subset_1(F_131,k1_zfmisc_1(k2_zfmisc_1(C_129,D_132)))
      | ~ v1_funct_1(F_131)
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_133)))
      | ~ v1_funct_1(E_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_626,plain,(
    ! [A_128,B_133,E_130] :
      ( k1_partfun1(A_128,B_133,'#skF_1','#skF_1',E_130,'#skF_5') = k5_relat_1(E_130,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_133)))
      | ~ v1_funct_1(E_130) ) ),
    inference(resolution,[status(thm)],[c_465,c_624])).

tff(c_635,plain,(
    ! [A_134,B_135,E_136] :
      ( k1_partfun1(A_134,B_135,'#skF_1','#skF_1',E_136,'#skF_5') = k5_relat_1(E_136,'#skF_5')
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_1(E_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_626])).

tff(c_641,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_466,c_635])).

tff(c_647,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_641])).

tff(c_391,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_371,c_34])).

tff(c_464,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_457,c_457,c_391])).

tff(c_652,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_464])).

tff(c_659,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_652,c_8])).

tff(c_665,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_40,c_404,c_46,c_547,c_463,c_659])).

tff(c_667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_665])).

tff(c_668,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_456])).

tff(c_681,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_668,c_382])).

tff(c_673,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_668,c_430])).

tff(c_677,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_668,c_390])).

tff(c_683,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_366])).

tff(c_755,plain,(
    ! [B_139,C_140] :
      ( k1_relset_1('#skF_4',B_139,C_140) = '#skF_4'
      | ~ v1_funct_2(C_140,'#skF_4',B_139)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_139))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_683,c_683,c_683,c_22])).

tff(c_758,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_677,c_755])).

tff(c_761,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_673,c_758])).

tff(c_675,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_414])).

tff(c_678,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_389])).

tff(c_829,plain,(
    ! [B_159,C_155,D_158,A_154,F_157,E_156] :
      ( k1_partfun1(A_154,B_159,C_155,D_158,E_156,F_157) = k5_relat_1(E_156,F_157)
      | ~ m1_subset_1(F_157,k1_zfmisc_1(k2_zfmisc_1(C_155,D_158)))
      | ~ v1_funct_1(F_157)
      | ~ m1_subset_1(E_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_159)))
      | ~ v1_funct_1(E_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_831,plain,(
    ! [A_154,B_159,E_156] :
      ( k1_partfun1(A_154,B_159,'#skF_4','#skF_4',E_156,'#skF_5') = k5_relat_1(E_156,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_159)))
      | ~ v1_funct_1(E_156) ) ),
    inference(resolution,[status(thm)],[c_677,c_829])).

tff(c_840,plain,(
    ! [A_160,B_161,E_162] :
      ( k1_partfun1(A_160,B_161,'#skF_4','#skF_4',E_162,'#skF_5') = k5_relat_1(E_162,'#skF_5')
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161)))
      | ~ v1_funct_1(E_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_831])).

tff(c_846,plain,
    ( k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_678,c_840])).

tff(c_852,plain,(
    k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_846])).

tff(c_676,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_668,c_668,c_391])).

tff(c_857,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_852,c_676])).

tff(c_867,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_857,c_8])).

tff(c_873,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_40,c_404,c_46,c_761,c_675,c_867])).

tff(c_875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_873])).

tff(c_876,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_886,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_36])).

tff(c_888,plain,(
    ! [B_165,A_166] :
      ( v1_relat_1(B_165)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(A_166))
      | ~ v1_relat_1(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_891,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_886,c_888])).

tff(c_897,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_891])).

tff(c_885,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_42])).

tff(c_894,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_885,c_888])).

tff(c_900,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_894])).

tff(c_939,plain,(
    ! [C_174,A_175] :
      ( C_174 = '#skF_3'
      | ~ v1_funct_2(C_174,A_175,'#skF_3')
      | A_175 = '#skF_3'
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_175,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_366,c_366,c_366,c_16])).

tff(c_945,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_885,c_939])).

tff(c_952,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_945])).

tff(c_953,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_952])).

tff(c_879,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_38])).

tff(c_964,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_953,c_879])).

tff(c_903,plain,(
    ! [A_168,B_169,C_170] :
      ( k1_relset_1(A_168,B_169,C_170) = k1_relat_1(C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_910,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_886,c_903])).

tff(c_958,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_953,c_910])).

tff(c_961,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_953,c_886])).

tff(c_967,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_366])).

tff(c_1018,plain,(
    ! [B_178,C_179] :
      ( k1_relset_1('#skF_1',B_178,C_179) = '#skF_1'
      | ~ v1_funct_2(C_179,'#skF_1',B_178)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_178))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_967,c_967,c_967,c_967,c_22])).

tff(c_1021,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_961,c_1018])).

tff(c_1024,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_964,c_958,c_1021])).

tff(c_880,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_371,c_32])).

tff(c_920,plain,(
    ! [A_171,B_172,C_173] :
      ( k2_relset_1(A_171,B_172,C_173) = k2_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_926,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_885,c_920])).

tff(c_929,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_926])).

tff(c_955,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_929])).

tff(c_962,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_885])).

tff(c_1129,plain,(
    ! [A_195,E_197,C_196,B_200,D_199,F_198] :
      ( k1_partfun1(A_195,B_200,C_196,D_199,E_197,F_198) = k5_relat_1(E_197,F_198)
      | ~ m1_subset_1(F_198,k1_zfmisc_1(k2_zfmisc_1(C_196,D_199)))
      | ~ v1_funct_1(F_198)
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_200)))
      | ~ v1_funct_1(E_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1133,plain,(
    ! [A_195,B_200,E_197] :
      ( k1_partfun1(A_195,B_200,'#skF_1','#skF_1',E_197,'#skF_5') = k5_relat_1(E_197,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_200)))
      | ~ v1_funct_1(E_197) ) ),
    inference(resolution,[status(thm)],[c_961,c_1129])).

tff(c_1161,plain,(
    ! [A_204,B_205,E_206] :
      ( k1_partfun1(A_204,B_205,'#skF_1','#skF_1',E_206,'#skF_5') = k5_relat_1(E_206,'#skF_5')
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(A_204,B_205)))
      | ~ v1_funct_1(E_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1133])).

tff(c_1164,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_962,c_1161])).

tff(c_1170,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1164])).

tff(c_887,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_371,c_34])).

tff(c_960,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_953,c_953,c_887])).

tff(c_1174,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1170,c_960])).

tff(c_1184,plain,
    ( v2_funct_1('#skF_5')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1174,c_6])).

tff(c_1190,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_40,c_900,c_46,c_1024,c_955,c_1184])).

tff(c_1192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_876,c_1190])).

tff(c_1193,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_952])).

tff(c_1205,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1193,c_1193,c_879])).

tff(c_1199,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1193,c_1193,c_910])).

tff(c_1202,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1193,c_1193,c_886])).

tff(c_1208,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1193,c_366])).

tff(c_1230,plain,(
    ! [B_16,C_17] :
      ( k1_relset_1('#skF_4',B_16,C_17) = '#skF_4'
      | ~ v1_funct_2(C_17,'#skF_4',B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_16))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_1208,c_1208,c_1208,c_22])).

tff(c_1238,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1202,c_1230])).

tff(c_1250,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_1199,c_1238])).

tff(c_1196,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1193,c_929])).

tff(c_1203,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1193,c_885])).

tff(c_1355,plain,(
    ! [D_228,C_225,A_224,F_227,B_229,E_226] :
      ( k1_partfun1(A_224,B_229,C_225,D_228,E_226,F_227) = k5_relat_1(E_226,F_227)
      | ~ m1_subset_1(F_227,k1_zfmisc_1(k2_zfmisc_1(C_225,D_228)))
      | ~ v1_funct_1(F_227)
      | ~ m1_subset_1(E_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_229)))
      | ~ v1_funct_1(E_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1359,plain,(
    ! [A_224,B_229,E_226] :
      ( k1_partfun1(A_224,B_229,'#skF_4','#skF_4',E_226,'#skF_5') = k5_relat_1(E_226,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_229)))
      | ~ v1_funct_1(E_226) ) ),
    inference(resolution,[status(thm)],[c_1202,c_1355])).

tff(c_1379,plain,(
    ! [A_233,B_234,E_235] :
      ( k1_partfun1(A_233,B_234,'#skF_4','#skF_4',E_235,'#skF_5') = k5_relat_1(E_235,'#skF_5')
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_1(E_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1359])).

tff(c_1382,plain,
    ( k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1203,c_1379])).

tff(c_1388,plain,(
    k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1382])).

tff(c_1201,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1193,c_1193,c_1193,c_887])).

tff(c_1400,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1388,c_1201])).

tff(c_1410,plain,
    ( v2_funct_1('#skF_5')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1400,c_6])).

tff(c_1416,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_40,c_900,c_46,c_1250,c_1196,c_1410])).

tff(c_1418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_876,c_1416])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:15:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.75  
% 3.69/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.75  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.69/1.75  
% 3.69/1.75  %Foreground sorts:
% 3.69/1.75  
% 3.69/1.75  
% 3.69/1.75  %Background operators:
% 3.69/1.75  
% 3.69/1.75  
% 3.69/1.75  %Foreground operators:
% 3.69/1.75  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.69/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.69/1.75  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.69/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.69/1.75  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.69/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.69/1.75  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.69/1.75  tff('#skF_5', type, '#skF_5': $i).
% 3.69/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.69/1.75  tff('#skF_2', type, '#skF_2': $i).
% 3.69/1.75  tff('#skF_3', type, '#skF_3': $i).
% 3.69/1.75  tff('#skF_1', type, '#skF_1': $i).
% 3.69/1.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.69/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.69/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.69/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.69/1.75  tff('#skF_4', type, '#skF_4': $i).
% 3.69/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.69/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.69/1.75  
% 3.69/1.79  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 3.69/1.79  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.69/1.79  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.69/1.79  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.69/1.79  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.69/1.79  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.69/1.79  tff(f_87, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.69/1.79  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 3.69/1.79  tff(c_28, plain, (~v2_funct_1('#skF_5') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.69/1.79  tff(c_381, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_28])).
% 3.69/1.79  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.69/1.79  tff(c_49, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_28])).
% 3.69/1.79  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.69/1.79  tff(c_54, plain, (![B_27, A_28]: (v1_relat_1(B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(A_28)) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.79  tff(c_57, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_54])).
% 3.69/1.79  tff(c_63, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_57])).
% 3.69/1.79  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.69/1.79  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.69/1.79  tff(c_60, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_54])).
% 3.69/1.79  tff(c_66, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_60])).
% 3.69/1.79  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.69/1.79  tff(c_30, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.69/1.79  tff(c_47, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_30])).
% 3.69/1.79  tff(c_38, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.69/1.79  tff(c_67, plain, (![A_29, B_30, C_31]: (k1_relset_1(A_29, B_30, C_31)=k1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.69/1.79  tff(c_74, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_67])).
% 3.69/1.79  tff(c_106, plain, (![B_42, A_43, C_44]: (k1_xboole_0=B_42 | k1_relset_1(A_43, B_42, C_44)=A_43 | ~v1_funct_2(C_44, A_43, B_42) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_43, B_42))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.69/1.79  tff(c_109, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_106])).
% 3.69/1.79  tff(c_115, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_74, c_109])).
% 3.69/1.79  tff(c_116, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_47, c_115])).
% 3.69/1.79  tff(c_32, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.69/1.79  tff(c_84, plain, (![A_32, B_33, C_34]: (k2_relset_1(A_32, B_33, C_34)=k2_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.69/1.79  tff(c_90, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_84])).
% 3.69/1.79  tff(c_93, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_90])).
% 3.69/1.79  tff(c_155, plain, (![D_56, E_54, B_57, A_52, F_55, C_53]: (k1_partfun1(A_52, B_57, C_53, D_56, E_54, F_55)=k5_relat_1(E_54, F_55) | ~m1_subset_1(F_55, k1_zfmisc_1(k2_zfmisc_1(C_53, D_56))) | ~v1_funct_1(F_55) | ~m1_subset_1(E_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_57))) | ~v1_funct_1(E_54))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.69/1.79  tff(c_157, plain, (![A_52, B_57, E_54]: (k1_partfun1(A_52, B_57, '#skF_2', '#skF_3', E_54, '#skF_5')=k5_relat_1(E_54, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_57))) | ~v1_funct_1(E_54))), inference(resolution, [status(thm)], [c_36, c_155])).
% 3.69/1.79  tff(c_166, plain, (![A_58, B_59, E_60]: (k1_partfun1(A_58, B_59, '#skF_2', '#skF_3', E_60, '#skF_5')=k5_relat_1(E_60, '#skF_5') | ~m1_subset_1(E_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_funct_1(E_60))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_157])).
% 3.69/1.79  tff(c_172, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_166])).
% 3.69/1.79  tff(c_178, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_172])).
% 3.69/1.79  tff(c_34, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.69/1.79  tff(c_183, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_34])).
% 3.69/1.79  tff(c_8, plain, (![B_8, A_6]: (v2_funct_1(B_8) | k2_relat_1(B_8)!=k1_relat_1(A_6) | ~v2_funct_1(k5_relat_1(B_8, A_6)) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.69/1.79  tff(c_190, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_183, c_8])).
% 3.69/1.79  tff(c_196, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_40, c_66, c_46, c_116, c_93, c_190])).
% 3.69/1.79  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_196])).
% 3.69/1.79  tff(c_199, plain, (~v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_28])).
% 3.69/1.79  tff(c_205, plain, (![B_61, A_62]: (v1_relat_1(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.79  tff(c_211, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_205])).
% 3.69/1.79  tff(c_217, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_211])).
% 3.69/1.79  tff(c_208, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_205])).
% 3.69/1.79  tff(c_214, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_208])).
% 3.69/1.79  tff(c_219, plain, (![A_64, B_65, C_66]: (k1_relset_1(A_64, B_65, C_66)=k1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.69/1.79  tff(c_227, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_219])).
% 3.69/1.79  tff(c_269, plain, (![B_79, A_80, C_81]: (k1_xboole_0=B_79 | k1_relset_1(A_80, B_79, C_81)=A_80 | ~v1_funct_2(C_81, A_80, B_79) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.69/1.79  tff(c_275, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_269])).
% 3.69/1.79  tff(c_281, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_227, c_275])).
% 3.69/1.79  tff(c_282, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_47, c_281])).
% 3.69/1.79  tff(c_236, plain, (![A_67, B_68, C_69]: (k2_relset_1(A_67, B_68, C_69)=k2_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.69/1.79  tff(c_239, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_236])).
% 3.69/1.79  tff(c_244, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_239])).
% 3.69/1.79  tff(c_304, plain, (![E_88, F_89, B_91, C_87, D_90, A_86]: (k1_partfun1(A_86, B_91, C_87, D_90, E_88, F_89)=k5_relat_1(E_88, F_89) | ~m1_subset_1(F_89, k1_zfmisc_1(k2_zfmisc_1(C_87, D_90))) | ~v1_funct_1(F_89) | ~m1_subset_1(E_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_91))) | ~v1_funct_1(E_88))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.69/1.79  tff(c_308, plain, (![A_86, B_91, E_88]: (k1_partfun1(A_86, B_91, '#skF_2', '#skF_3', E_88, '#skF_5')=k5_relat_1(E_88, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_91))) | ~v1_funct_1(E_88))), inference(resolution, [status(thm)], [c_36, c_304])).
% 3.69/1.79  tff(c_336, plain, (![A_95, B_96, E_97]: (k1_partfun1(A_95, B_96, '#skF_2', '#skF_3', E_97, '#skF_5')=k5_relat_1(E_97, '#skF_5') | ~m1_subset_1(E_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_1(E_97))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_308])).
% 3.69/1.79  tff(c_339, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_336])).
% 3.69/1.79  tff(c_345, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_339])).
% 3.69/1.79  tff(c_349, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_345, c_34])).
% 3.69/1.79  tff(c_6, plain, (![A_6, B_8]: (v2_funct_1(A_6) | k2_relat_1(B_8)!=k1_relat_1(A_6) | ~v2_funct_1(k5_relat_1(B_8, A_6)) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.69/1.79  tff(c_356, plain, (v2_funct_1('#skF_5') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_349, c_6])).
% 3.69/1.79  tff(c_362, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_40, c_214, c_46, c_282, c_244, c_356])).
% 3.69/1.79  tff(c_364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_199, c_362])).
% 3.69/1.79  tff(c_366, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 3.69/1.79  tff(c_365, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 3.69/1.79  tff(c_371, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_366, c_365])).
% 3.69/1.79  tff(c_390, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_36])).
% 3.69/1.79  tff(c_392, plain, (![B_100, A_101]: (v1_relat_1(B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(A_101)) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.79  tff(c_395, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_390, c_392])).
% 3.69/1.79  tff(c_401, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_395])).
% 3.69/1.79  tff(c_389, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_42])).
% 3.69/1.79  tff(c_398, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_389, c_392])).
% 3.69/1.79  tff(c_404, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_398])).
% 3.69/1.79  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.69/1.79  tff(c_376, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_371, c_44])).
% 3.69/1.79  tff(c_16, plain, (![C_17, A_15]: (k1_xboole_0=C_17 | ~v1_funct_2(C_17, A_15, k1_xboole_0) | k1_xboole_0=A_15 | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.69/1.79  tff(c_443, plain, (![C_109, A_110]: (C_109='#skF_3' | ~v1_funct_2(C_109, A_110, '#skF_3') | A_110='#skF_3' | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_366, c_366, c_366, c_16])).
% 3.69/1.79  tff(c_449, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_389, c_443])).
% 3.69/1.79  tff(c_456, plain, ('#skF_3'='#skF_4' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_376, c_449])).
% 3.69/1.79  tff(c_457, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_456])).
% 3.69/1.79  tff(c_382, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_371, c_38])).
% 3.69/1.79  tff(c_469, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_457, c_382])).
% 3.69/1.79  tff(c_465, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_457, c_390])).
% 3.69/1.79  tff(c_471, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_457, c_366])).
% 3.69/1.79  tff(c_22, plain, (![B_16, C_17]: (k1_relset_1(k1_xboole_0, B_16, C_17)=k1_xboole_0 | ~v1_funct_2(C_17, k1_xboole_0, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_16))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.69/1.79  tff(c_488, plain, (![B_16, C_17]: (k1_relset_1('#skF_1', B_16, C_17)='#skF_1' | ~v1_funct_2(C_17, '#skF_1', B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_16))))), inference(demodulation, [status(thm), theory('equality')], [c_471, c_471, c_471, c_471, c_22])).
% 3.69/1.79  tff(c_521, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_465, c_488])).
% 3.69/1.79  tff(c_533, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_469, c_521])).
% 3.69/1.79  tff(c_423, plain, (![A_105, B_106, C_107]: (k1_relset_1(A_105, B_106, C_107)=k1_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.69/1.79  tff(c_430, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_390, c_423])).
% 3.69/1.79  tff(c_461, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_457, c_430])).
% 3.69/1.79  tff(c_547, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_533, c_461])).
% 3.69/1.79  tff(c_384, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_371, c_371, c_32])).
% 3.69/1.79  tff(c_405, plain, (![A_102, B_103, C_104]: (k2_relset_1(A_102, B_103, C_104)=k2_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.69/1.79  tff(c_411, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_389, c_405])).
% 3.69/1.79  tff(c_414, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_384, c_411])).
% 3.69/1.79  tff(c_463, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_457, c_414])).
% 3.69/1.79  tff(c_466, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_389])).
% 3.69/1.79  tff(c_624, plain, (![B_133, E_130, F_131, A_128, D_132, C_129]: (k1_partfun1(A_128, B_133, C_129, D_132, E_130, F_131)=k5_relat_1(E_130, F_131) | ~m1_subset_1(F_131, k1_zfmisc_1(k2_zfmisc_1(C_129, D_132))) | ~v1_funct_1(F_131) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_133))) | ~v1_funct_1(E_130))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.69/1.79  tff(c_626, plain, (![A_128, B_133, E_130]: (k1_partfun1(A_128, B_133, '#skF_1', '#skF_1', E_130, '#skF_5')=k5_relat_1(E_130, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_133))) | ~v1_funct_1(E_130))), inference(resolution, [status(thm)], [c_465, c_624])).
% 3.69/1.79  tff(c_635, plain, (![A_134, B_135, E_136]: (k1_partfun1(A_134, B_135, '#skF_1', '#skF_1', E_136, '#skF_5')=k5_relat_1(E_136, '#skF_5') | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_1(E_136))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_626])).
% 3.69/1.79  tff(c_641, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_466, c_635])).
% 3.69/1.79  tff(c_647, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_641])).
% 3.69/1.79  tff(c_391, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_371, c_34])).
% 3.69/1.79  tff(c_464, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_457, c_457, c_391])).
% 3.69/1.79  tff(c_652, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_647, c_464])).
% 3.69/1.79  tff(c_659, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_652, c_8])).
% 3.69/1.79  tff(c_665, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_401, c_40, c_404, c_46, c_547, c_463, c_659])).
% 3.69/1.79  tff(c_667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_665])).
% 3.69/1.79  tff(c_668, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_456])).
% 3.69/1.79  tff(c_681, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_668, c_668, c_382])).
% 3.69/1.79  tff(c_673, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_668, c_668, c_430])).
% 3.69/1.79  tff(c_677, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_668, c_668, c_390])).
% 3.69/1.79  tff(c_683, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_668, c_366])).
% 3.69/1.79  tff(c_755, plain, (![B_139, C_140]: (k1_relset_1('#skF_4', B_139, C_140)='#skF_4' | ~v1_funct_2(C_140, '#skF_4', B_139) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_139))))), inference(demodulation, [status(thm), theory('equality')], [c_683, c_683, c_683, c_683, c_22])).
% 3.69/1.79  tff(c_758, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_677, c_755])).
% 3.69/1.79  tff(c_761, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_681, c_673, c_758])).
% 3.69/1.79  tff(c_675, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_668, c_414])).
% 3.69/1.79  tff(c_678, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_668, c_389])).
% 3.69/1.79  tff(c_829, plain, (![B_159, C_155, D_158, A_154, F_157, E_156]: (k1_partfun1(A_154, B_159, C_155, D_158, E_156, F_157)=k5_relat_1(E_156, F_157) | ~m1_subset_1(F_157, k1_zfmisc_1(k2_zfmisc_1(C_155, D_158))) | ~v1_funct_1(F_157) | ~m1_subset_1(E_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_159))) | ~v1_funct_1(E_156))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.69/1.79  tff(c_831, plain, (![A_154, B_159, E_156]: (k1_partfun1(A_154, B_159, '#skF_4', '#skF_4', E_156, '#skF_5')=k5_relat_1(E_156, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_159))) | ~v1_funct_1(E_156))), inference(resolution, [status(thm)], [c_677, c_829])).
% 3.69/1.79  tff(c_840, plain, (![A_160, B_161, E_162]: (k1_partfun1(A_160, B_161, '#skF_4', '#skF_4', E_162, '#skF_5')=k5_relat_1(E_162, '#skF_5') | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))) | ~v1_funct_1(E_162))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_831])).
% 3.69/1.79  tff(c_846, plain, (k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_678, c_840])).
% 3.69/1.79  tff(c_852, plain, (k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_846])).
% 3.69/1.79  tff(c_676, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_668, c_668, c_668, c_391])).
% 3.69/1.79  tff(c_857, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_852, c_676])).
% 3.69/1.79  tff(c_867, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_857, c_8])).
% 3.69/1.79  tff(c_873, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_401, c_40, c_404, c_46, c_761, c_675, c_867])).
% 3.69/1.79  tff(c_875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_873])).
% 3.69/1.79  tff(c_876, plain, (~v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_28])).
% 3.69/1.79  tff(c_886, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_36])).
% 3.69/1.79  tff(c_888, plain, (![B_165, A_166]: (v1_relat_1(B_165) | ~m1_subset_1(B_165, k1_zfmisc_1(A_166)) | ~v1_relat_1(A_166))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.69/1.79  tff(c_891, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_886, c_888])).
% 3.69/1.79  tff(c_897, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_891])).
% 3.69/1.79  tff(c_885, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_42])).
% 3.69/1.79  tff(c_894, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_885, c_888])).
% 3.69/1.79  tff(c_900, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_894])).
% 3.69/1.79  tff(c_939, plain, (![C_174, A_175]: (C_174='#skF_3' | ~v1_funct_2(C_174, A_175, '#skF_3') | A_175='#skF_3' | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_175, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_366, c_366, c_366, c_366, c_16])).
% 3.69/1.79  tff(c_945, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_885, c_939])).
% 3.69/1.79  tff(c_952, plain, ('#skF_3'='#skF_4' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_376, c_945])).
% 3.69/1.79  tff(c_953, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_952])).
% 3.69/1.79  tff(c_879, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_371, c_38])).
% 3.69/1.79  tff(c_964, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_953, c_953, c_879])).
% 3.69/1.79  tff(c_903, plain, (![A_168, B_169, C_170]: (k1_relset_1(A_168, B_169, C_170)=k1_relat_1(C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.69/1.79  tff(c_910, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_886, c_903])).
% 3.69/1.79  tff(c_958, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_953, c_953, c_910])).
% 3.69/1.79  tff(c_961, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_953, c_953, c_886])).
% 3.69/1.79  tff(c_967, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_953, c_366])).
% 3.69/1.79  tff(c_1018, plain, (![B_178, C_179]: (k1_relset_1('#skF_1', B_178, C_179)='#skF_1' | ~v1_funct_2(C_179, '#skF_1', B_178) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_178))))), inference(demodulation, [status(thm), theory('equality')], [c_967, c_967, c_967, c_967, c_22])).
% 3.69/1.79  tff(c_1021, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_961, c_1018])).
% 3.69/1.79  tff(c_1024, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_964, c_958, c_1021])).
% 3.69/1.79  tff(c_880, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_371, c_371, c_32])).
% 3.69/1.79  tff(c_920, plain, (![A_171, B_172, C_173]: (k2_relset_1(A_171, B_172, C_173)=k2_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.69/1.79  tff(c_926, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_885, c_920])).
% 3.69/1.79  tff(c_929, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_880, c_926])).
% 3.69/1.79  tff(c_955, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_953, c_929])).
% 3.69/1.79  tff(c_962, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_953, c_885])).
% 3.69/1.79  tff(c_1129, plain, (![A_195, E_197, C_196, B_200, D_199, F_198]: (k1_partfun1(A_195, B_200, C_196, D_199, E_197, F_198)=k5_relat_1(E_197, F_198) | ~m1_subset_1(F_198, k1_zfmisc_1(k2_zfmisc_1(C_196, D_199))) | ~v1_funct_1(F_198) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_200))) | ~v1_funct_1(E_197))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.69/1.79  tff(c_1133, plain, (![A_195, B_200, E_197]: (k1_partfun1(A_195, B_200, '#skF_1', '#skF_1', E_197, '#skF_5')=k5_relat_1(E_197, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_200))) | ~v1_funct_1(E_197))), inference(resolution, [status(thm)], [c_961, c_1129])).
% 3.69/1.79  tff(c_1161, plain, (![A_204, B_205, E_206]: (k1_partfun1(A_204, B_205, '#skF_1', '#skF_1', E_206, '#skF_5')=k5_relat_1(E_206, '#skF_5') | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(A_204, B_205))) | ~v1_funct_1(E_206))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1133])).
% 3.69/1.79  tff(c_1164, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_962, c_1161])).
% 3.69/1.79  tff(c_1170, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1164])).
% 3.69/1.79  tff(c_887, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_371, c_34])).
% 3.69/1.79  tff(c_960, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_953, c_953, c_953, c_887])).
% 3.69/1.79  tff(c_1174, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1170, c_960])).
% 3.69/1.79  tff(c_1184, plain, (v2_funct_1('#skF_5') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1174, c_6])).
% 3.69/1.79  tff(c_1190, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_897, c_40, c_900, c_46, c_1024, c_955, c_1184])).
% 3.69/1.79  tff(c_1192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_876, c_1190])).
% 3.69/1.79  tff(c_1193, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_952])).
% 3.69/1.79  tff(c_1205, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1193, c_1193, c_879])).
% 3.69/1.79  tff(c_1199, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1193, c_1193, c_910])).
% 3.69/1.79  tff(c_1202, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1193, c_1193, c_886])).
% 3.69/1.79  tff(c_1208, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1193, c_366])).
% 3.69/1.79  tff(c_1230, plain, (![B_16, C_17]: (k1_relset_1('#skF_4', B_16, C_17)='#skF_4' | ~v1_funct_2(C_17, '#skF_4', B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_16))))), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_1208, c_1208, c_1208, c_22])).
% 3.69/1.79  tff(c_1238, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_1202, c_1230])).
% 3.69/1.79  tff(c_1250, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_1199, c_1238])).
% 3.69/1.79  tff(c_1196, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1193, c_929])).
% 3.69/1.79  tff(c_1203, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1193, c_885])).
% 3.69/1.79  tff(c_1355, plain, (![D_228, C_225, A_224, F_227, B_229, E_226]: (k1_partfun1(A_224, B_229, C_225, D_228, E_226, F_227)=k5_relat_1(E_226, F_227) | ~m1_subset_1(F_227, k1_zfmisc_1(k2_zfmisc_1(C_225, D_228))) | ~v1_funct_1(F_227) | ~m1_subset_1(E_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_229))) | ~v1_funct_1(E_226))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.69/1.79  tff(c_1359, plain, (![A_224, B_229, E_226]: (k1_partfun1(A_224, B_229, '#skF_4', '#skF_4', E_226, '#skF_5')=k5_relat_1(E_226, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_229))) | ~v1_funct_1(E_226))), inference(resolution, [status(thm)], [c_1202, c_1355])).
% 3.69/1.79  tff(c_1379, plain, (![A_233, B_234, E_235]: (k1_partfun1(A_233, B_234, '#skF_4', '#skF_4', E_235, '#skF_5')=k5_relat_1(E_235, '#skF_5') | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_1(E_235))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1359])).
% 3.69/1.79  tff(c_1382, plain, (k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1203, c_1379])).
% 3.69/1.79  tff(c_1388, plain, (k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1382])).
% 3.69/1.79  tff(c_1201, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1193, c_1193, c_1193, c_887])).
% 3.69/1.79  tff(c_1400, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1388, c_1201])).
% 3.69/1.79  tff(c_1410, plain, (v2_funct_1('#skF_5') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1400, c_6])).
% 3.69/1.79  tff(c_1416, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_897, c_40, c_900, c_46, c_1250, c_1196, c_1410])).
% 3.69/1.79  tff(c_1418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_876, c_1416])).
% 3.69/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.79  
% 3.69/1.79  Inference rules
% 3.69/1.79  ----------------------
% 3.69/1.79  #Ref     : 0
% 3.69/1.79  #Sup     : 316
% 3.69/1.79  #Fact    : 0
% 3.69/1.79  #Define  : 0
% 3.69/1.79  #Split   : 7
% 3.69/1.79  #Chain   : 0
% 3.69/1.79  #Close   : 0
% 3.69/1.79  
% 3.69/1.79  Ordering : KBO
% 3.69/1.79  
% 3.69/1.79  Simplification rules
% 3.69/1.79  ----------------------
% 3.69/1.79  #Subsume      : 0
% 3.69/1.79  #Demod        : 425
% 3.69/1.79  #Tautology    : 240
% 3.69/1.79  #SimpNegUnit  : 14
% 3.69/1.79  #BackRed      : 73
% 3.69/1.79  
% 3.69/1.79  #Partial instantiations: 0
% 3.69/1.79  #Strategies tried      : 1
% 3.69/1.79  
% 3.69/1.79  Timing (in seconds)
% 3.69/1.79  ----------------------
% 3.69/1.79  Preprocessing        : 0.38
% 3.69/1.79  Parsing              : 0.21
% 3.69/1.79  CNF conversion       : 0.03
% 3.69/1.79  Main loop            : 0.53
% 3.69/1.79  Inferencing          : 0.20
% 3.69/1.79  Reduction            : 0.18
% 3.69/1.79  Demodulation         : 0.12
% 3.69/1.79  BG Simplification    : 0.03
% 3.69/1.79  Subsumption          : 0.07
% 3.69/1.79  Abstraction          : 0.02
% 3.69/1.79  MUC search           : 0.00
% 3.69/1.79  Cooper               : 0.00
% 3.69/1.79  Total                : 1.00
% 3.69/1.79  Index Insertion      : 0.00
% 3.69/1.79  Index Deletion       : 0.00
% 3.69/1.79  Index Matching       : 0.00
% 3.69/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
