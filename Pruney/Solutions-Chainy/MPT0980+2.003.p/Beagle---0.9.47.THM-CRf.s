%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:54 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  134 (1031 expanded)
%              Number of leaves         :   33 ( 321 expanded)
%              Depth                    :   16
%              Number of atoms          :  278 (3941 expanded)
%              Number of equality atoms :   58 (1387 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C,D] :
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
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

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

tff(c_32,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_51,plain,(
    ! [B_29,A_30] :
      ( v1_relat_1(B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_51])).

tff(c_60,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_54])).

tff(c_64,plain,(
    ! [C_31,B_32,A_33] :
      ( v5_relat_1(C_31,B_32)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_33,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_71,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_64])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_197,plain,(
    ! [B_66,F_70,D_67,C_65,E_68,A_69] :
      ( k1_partfun1(A_69,B_66,C_65,D_67,E_68,F_70) = k5_relat_1(E_68,F_70)
      | ~ m1_subset_1(F_70,k1_zfmisc_1(k2_zfmisc_1(C_65,D_67)))
      | ~ v1_funct_1(F_70)
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_66)))
      | ~ v1_funct_1(E_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_201,plain,(
    ! [A_69,B_66,E_68] :
      ( k1_partfun1(A_69,B_66,'#skF_2','#skF_3',E_68,'#skF_5') = k5_relat_1(E_68,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_66)))
      | ~ v1_funct_1(E_68) ) ),
    inference(resolution,[status(thm)],[c_38,c_197])).

tff(c_225,plain,(
    ! [A_74,B_75,E_76] :
      ( k1_partfun1(A_74,B_75,'#skF_2','#skF_3',E_76,'#skF_5') = k5_relat_1(E_76,'#skF_5')
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_funct_1(E_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_201])).

tff(c_228,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_225])).

tff(c_234,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_228])).

tff(c_36,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_246,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_36])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_57,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_51])).

tff(c_63,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_57])).

tff(c_34,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_49,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_40,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_89,plain,(
    ! [A_42,B_43,C_44] :
      ( k1_relset_1(A_42,B_43,C_44) = k1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_97,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_89])).

tff(c_109,plain,(
    ! [B_51,A_52,C_53] :
      ( k1_xboole_0 = B_51
      | k1_relset_1(A_52,B_51,C_53) = A_52
      | ~ v1_funct_2(C_53,A_52,B_51)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_115,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_109])).

tff(c_121,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_97,c_115])).

tff(c_122,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_121])).

tff(c_156,plain,(
    ! [B_57,A_58] :
      ( v2_funct_1(B_57)
      | ~ r1_tarski(k2_relat_1(B_57),k1_relat_1(A_58))
      | ~ v2_funct_1(k5_relat_1(B_57,A_58))
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_162,plain,(
    ! [B_57] :
      ( v2_funct_1(B_57)
      | ~ r1_tarski(k2_relat_1(B_57),'#skF_2')
      | ~ v2_funct_1(k5_relat_1(B_57,'#skF_5'))
      | ~ v1_funct_1(B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_156])).

tff(c_179,plain,(
    ! [B_61] :
      ( v2_funct_1(B_61)
      | ~ r1_tarski(k2_relat_1(B_61),'#skF_2')
      | ~ v2_funct_1(k5_relat_1(B_61,'#skF_5'))
      | ~ v1_funct_1(B_61)
      | ~ v1_relat_1(B_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_42,c_162])).

tff(c_184,plain,(
    ! [B_5] :
      ( v2_funct_1(B_5)
      | ~ v2_funct_1(k5_relat_1(B_5,'#skF_5'))
      | ~ v1_funct_1(B_5)
      | ~ v5_relat_1(B_5,'#skF_2')
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_179])).

tff(c_253,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_246,c_184])).

tff(c_256,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_71,c_48,c_253])).

tff(c_258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_256])).

tff(c_260,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_259,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_265,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_259])).

tff(c_278,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_44])).

tff(c_280,plain,(
    ! [B_79,A_80] :
      ( v1_relat_1(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_80))
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_283,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_278,c_280])).

tff(c_289,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_283])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_274,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_46])).

tff(c_20,plain,(
    ! [C_19,A_17] :
      ( k1_xboole_0 = C_19
      | ~ v1_funct_2(C_19,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_337,plain,(
    ! [C_95,A_96] :
      ( C_95 = '#skF_3'
      | ~ v1_funct_2(C_95,A_96,'#skF_3')
      | A_96 = '#skF_3'
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_260,c_260,c_260,c_20])).

tff(c_340,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_278,c_337])).

tff(c_346,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_340])).

tff(c_364,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_293,plain,(
    ! [C_81,B_82,A_83] :
      ( v5_relat_1(C_81,B_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_300,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_278,c_293])).

tff(c_372,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_300])).

tff(c_374,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_278])).

tff(c_277,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_38])).

tff(c_375,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_364,c_277])).

tff(c_559,plain,(
    ! [B_118,A_121,D_119,F_122,C_117,E_120] :
      ( k1_partfun1(A_121,B_118,C_117,D_119,E_120,F_122) = k5_relat_1(E_120,F_122)
      | ~ m1_subset_1(F_122,k1_zfmisc_1(k2_zfmisc_1(C_117,D_119)))
      | ~ v1_funct_1(F_122)
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_118)))
      | ~ v1_funct_1(E_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_561,plain,(
    ! [A_121,B_118,E_120] :
      ( k1_partfun1(A_121,B_118,'#skF_1','#skF_1',E_120,'#skF_5') = k5_relat_1(E_120,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_118)))
      | ~ v1_funct_1(E_120) ) ),
    inference(resolution,[status(thm)],[c_375,c_559])).

tff(c_582,plain,(
    ! [A_126,B_127,E_128] :
      ( k1_partfun1(A_126,B_127,'#skF_1','#skF_1',E_128,'#skF_5') = k5_relat_1(E_128,'#skF_5')
      | ~ m1_subset_1(E_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_1(E_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_561])).

tff(c_588,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_374,c_582])).

tff(c_594,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_588])).

tff(c_279,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_265,c_36])).

tff(c_373,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_364,c_364,c_279])).

tff(c_599,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_373])).

tff(c_286,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_277,c_280])).

tff(c_292,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_286])).

tff(c_276,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_40])).

tff(c_319,plain,(
    ! [A_92,B_93,C_94] :
      ( k1_relset_1(A_92,B_93,C_94) = k1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_327,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_277,c_319])).

tff(c_26,plain,(
    ! [B_18,C_19] :
      ( k1_relset_1(k1_xboole_0,B_18,C_19) = k1_xboole_0
      | ~ v1_funct_2(C_19,k1_xboole_0,B_18)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_352,plain,(
    ! [B_97,C_98] :
      ( k1_relset_1('#skF_3',B_97,C_98) = '#skF_3'
      | ~ v1_funct_2(C_98,'#skF_3',B_97)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_97))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_260,c_260,c_260,c_26])).

tff(c_355,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_277,c_352])).

tff(c_358,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_327,c_355])).

tff(c_365,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_358])).

tff(c_530,plain,(
    ! [B_112,A_113] :
      ( v2_funct_1(B_112)
      | ~ r1_tarski(k2_relat_1(B_112),k1_relat_1(A_113))
      | ~ v2_funct_1(k5_relat_1(B_112,A_113))
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_536,plain,(
    ! [B_112] :
      ( v2_funct_1(B_112)
      | ~ r1_tarski(k2_relat_1(B_112),'#skF_1')
      | ~ v2_funct_1(k5_relat_1(B_112,'#skF_5'))
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_530])).

tff(c_546,plain,(
    ! [B_114] :
      ( v2_funct_1(B_114)
      | ~ r1_tarski(k2_relat_1(B_114),'#skF_1')
      | ~ v2_funct_1(k5_relat_1(B_114,'#skF_5'))
      | ~ v1_funct_1(B_114)
      | ~ v1_relat_1(B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_42,c_536])).

tff(c_551,plain,(
    ! [B_5] :
      ( v2_funct_1(B_5)
      | ~ v2_funct_1(k5_relat_1(B_5,'#skF_5'))
      | ~ v1_funct_1(B_5)
      | ~ v5_relat_1(B_5,'#skF_1')
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_546])).

tff(c_606,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_599,c_551])).

tff(c_609,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_372,c_48,c_606])).

tff(c_611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_609])).

tff(c_612,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_621,plain,(
    v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_300])).

tff(c_623,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_278])).

tff(c_624,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_612,c_277])).

tff(c_778,plain,(
    ! [E_149,D_148,B_147,A_150,F_151,C_146] :
      ( k1_partfun1(A_150,B_147,C_146,D_148,E_149,F_151) = k5_relat_1(E_149,F_151)
      | ~ m1_subset_1(F_151,k1_zfmisc_1(k2_zfmisc_1(C_146,D_148)))
      | ~ v1_funct_1(F_151)
      | ~ m1_subset_1(E_149,k1_zfmisc_1(k2_zfmisc_1(A_150,B_147)))
      | ~ v1_funct_1(E_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_782,plain,(
    ! [A_150,B_147,E_149] :
      ( k1_partfun1(A_150,B_147,'#skF_4','#skF_4',E_149,'#skF_5') = k5_relat_1(E_149,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_149,k1_zfmisc_1(k2_zfmisc_1(A_150,B_147)))
      | ~ v1_funct_1(E_149) ) ),
    inference(resolution,[status(thm)],[c_624,c_778])).

tff(c_823,plain,(
    ! [A_159,B_160,E_161] :
      ( k1_partfun1(A_159,B_160,'#skF_4','#skF_4',E_161,'#skF_5') = k5_relat_1(E_161,'#skF_5')
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160)))
      | ~ v1_funct_1(E_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_782])).

tff(c_826,plain,
    ( k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_623,c_823])).

tff(c_832,plain,(
    k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_826])).

tff(c_622,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_612,c_612,c_279])).

tff(c_836,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_622])).

tff(c_614,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_358])).

tff(c_767,plain,(
    ! [B_144,A_145] :
      ( v2_funct_1(B_144)
      | ~ r1_tarski(k2_relat_1(B_144),k1_relat_1(A_145))
      | ~ v2_funct_1(k5_relat_1(B_144,A_145))
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_funct_1(A_145)
      | ~ v1_relat_1(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_770,plain,(
    ! [B_144] :
      ( v2_funct_1(B_144)
      | ~ r1_tarski(k2_relat_1(B_144),'#skF_4')
      | ~ v2_funct_1(k5_relat_1(B_144,'#skF_5'))
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_767])).

tff(c_789,plain,(
    ! [B_152] :
      ( v2_funct_1(B_152)
      | ~ r1_tarski(k2_relat_1(B_152),'#skF_4')
      | ~ v2_funct_1(k5_relat_1(B_152,'#skF_5'))
      | ~ v1_funct_1(B_152)
      | ~ v1_relat_1(B_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_42,c_770])).

tff(c_794,plain,(
    ! [B_5] :
      ( v2_funct_1(B_5)
      | ~ v2_funct_1(k5_relat_1(B_5,'#skF_5'))
      | ~ v1_funct_1(B_5)
      | ~ v5_relat_1(B_5,'#skF_4')
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_789])).

tff(c_843,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v5_relat_1('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_836,c_794])).

tff(c_846,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_621,c_48,c_843])).

tff(c_848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_846])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.55  
% 3.32/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.56  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.32/1.56  
% 3.32/1.56  %Foreground sorts:
% 3.32/1.56  
% 3.32/1.56  
% 3.32/1.56  %Background operators:
% 3.32/1.56  
% 3.32/1.56  
% 3.32/1.56  %Foreground operators:
% 3.32/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.32/1.56  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.32/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.32/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.32/1.56  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.32/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.32/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.56  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.32/1.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.32/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.32/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.32/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.56  
% 3.32/1.58  tff(f_116, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 3.32/1.58  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.32/1.58  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.32/1.58  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.32/1.58  tff(f_93, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.32/1.58  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.32/1.58  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.32/1.58  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.32/1.58  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_1)).
% 3.32/1.58  tff(c_32, plain, (~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.32/1.58  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.32/1.58  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.32/1.58  tff(c_51, plain, (![B_29, A_30]: (v1_relat_1(B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.32/1.58  tff(c_54, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_51])).
% 3.32/1.58  tff(c_60, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_54])).
% 3.32/1.58  tff(c_64, plain, (![C_31, B_32, A_33]: (v5_relat_1(C_31, B_32) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_33, B_32))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.32/1.58  tff(c_71, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_64])).
% 3.32/1.58  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.32/1.58  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.32/1.58  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.32/1.58  tff(c_197, plain, (![B_66, F_70, D_67, C_65, E_68, A_69]: (k1_partfun1(A_69, B_66, C_65, D_67, E_68, F_70)=k5_relat_1(E_68, F_70) | ~m1_subset_1(F_70, k1_zfmisc_1(k2_zfmisc_1(C_65, D_67))) | ~v1_funct_1(F_70) | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_66))) | ~v1_funct_1(E_68))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.32/1.58  tff(c_201, plain, (![A_69, B_66, E_68]: (k1_partfun1(A_69, B_66, '#skF_2', '#skF_3', E_68, '#skF_5')=k5_relat_1(E_68, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_66))) | ~v1_funct_1(E_68))), inference(resolution, [status(thm)], [c_38, c_197])).
% 3.32/1.58  tff(c_225, plain, (![A_74, B_75, E_76]: (k1_partfun1(A_74, B_75, '#skF_2', '#skF_3', E_76, '#skF_5')=k5_relat_1(E_76, '#skF_5') | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_funct_1(E_76))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_201])).
% 3.32/1.58  tff(c_228, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_225])).
% 3.32/1.58  tff(c_234, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_228])).
% 3.32/1.58  tff(c_36, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.32/1.58  tff(c_246, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_36])).
% 3.32/1.58  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.32/1.58  tff(c_57, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_51])).
% 3.32/1.58  tff(c_63, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_57])).
% 3.32/1.58  tff(c_34, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.32/1.58  tff(c_49, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_34])).
% 3.32/1.58  tff(c_40, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.32/1.58  tff(c_89, plain, (![A_42, B_43, C_44]: (k1_relset_1(A_42, B_43, C_44)=k1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.32/1.58  tff(c_97, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_89])).
% 3.32/1.58  tff(c_109, plain, (![B_51, A_52, C_53]: (k1_xboole_0=B_51 | k1_relset_1(A_52, B_51, C_53)=A_52 | ~v1_funct_2(C_53, A_52, B_51) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.32/1.58  tff(c_115, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_109])).
% 3.32/1.58  tff(c_121, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_97, c_115])).
% 3.32/1.58  tff(c_122, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_49, c_121])).
% 3.32/1.58  tff(c_156, plain, (![B_57, A_58]: (v2_funct_1(B_57) | ~r1_tarski(k2_relat_1(B_57), k1_relat_1(A_58)) | ~v2_funct_1(k5_relat_1(B_57, A_58)) | ~v1_funct_1(B_57) | ~v1_relat_1(B_57) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.32/1.58  tff(c_162, plain, (![B_57]: (v2_funct_1(B_57) | ~r1_tarski(k2_relat_1(B_57), '#skF_2') | ~v2_funct_1(k5_relat_1(B_57, '#skF_5')) | ~v1_funct_1(B_57) | ~v1_relat_1(B_57) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_122, c_156])).
% 3.32/1.58  tff(c_179, plain, (![B_61]: (v2_funct_1(B_61) | ~r1_tarski(k2_relat_1(B_61), '#skF_2') | ~v2_funct_1(k5_relat_1(B_61, '#skF_5')) | ~v1_funct_1(B_61) | ~v1_relat_1(B_61))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_42, c_162])).
% 3.32/1.58  tff(c_184, plain, (![B_5]: (v2_funct_1(B_5) | ~v2_funct_1(k5_relat_1(B_5, '#skF_5')) | ~v1_funct_1(B_5) | ~v5_relat_1(B_5, '#skF_2') | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_179])).
% 3.32/1.58  tff(c_253, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_246, c_184])).
% 3.32/1.58  tff(c_256, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_71, c_48, c_253])).
% 3.32/1.58  tff(c_258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_256])).
% 3.32/1.58  tff(c_260, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 3.32/1.58  tff(c_259, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 3.32/1.58  tff(c_265, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_260, c_259])).
% 3.32/1.58  tff(c_278, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_44])).
% 3.32/1.58  tff(c_280, plain, (![B_79, A_80]: (v1_relat_1(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_80)) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.32/1.58  tff(c_283, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_278, c_280])).
% 3.32/1.58  tff(c_289, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_283])).
% 3.32/1.58  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.32/1.58  tff(c_274, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_46])).
% 3.32/1.58  tff(c_20, plain, (![C_19, A_17]: (k1_xboole_0=C_19 | ~v1_funct_2(C_19, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.32/1.58  tff(c_337, plain, (![C_95, A_96]: (C_95='#skF_3' | ~v1_funct_2(C_95, A_96, '#skF_3') | A_96='#skF_3' | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_260, c_260, c_260, c_20])).
% 3.32/1.58  tff(c_340, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_278, c_337])).
% 3.32/1.58  tff(c_346, plain, ('#skF_3'='#skF_4' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_274, c_340])).
% 3.32/1.58  tff(c_364, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_346])).
% 3.32/1.58  tff(c_293, plain, (![C_81, B_82, A_83]: (v5_relat_1(C_81, B_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.32/1.58  tff(c_300, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_278, c_293])).
% 3.32/1.58  tff(c_372, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_364, c_300])).
% 3.32/1.58  tff(c_374, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_364, c_278])).
% 3.32/1.58  tff(c_277, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_38])).
% 3.32/1.58  tff(c_375, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_364, c_364, c_277])).
% 3.32/1.58  tff(c_559, plain, (![B_118, A_121, D_119, F_122, C_117, E_120]: (k1_partfun1(A_121, B_118, C_117, D_119, E_120, F_122)=k5_relat_1(E_120, F_122) | ~m1_subset_1(F_122, k1_zfmisc_1(k2_zfmisc_1(C_117, D_119))) | ~v1_funct_1(F_122) | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_118))) | ~v1_funct_1(E_120))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.32/1.58  tff(c_561, plain, (![A_121, B_118, E_120]: (k1_partfun1(A_121, B_118, '#skF_1', '#skF_1', E_120, '#skF_5')=k5_relat_1(E_120, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_118))) | ~v1_funct_1(E_120))), inference(resolution, [status(thm)], [c_375, c_559])).
% 3.32/1.58  tff(c_582, plain, (![A_126, B_127, E_128]: (k1_partfun1(A_126, B_127, '#skF_1', '#skF_1', E_128, '#skF_5')=k5_relat_1(E_128, '#skF_5') | ~m1_subset_1(E_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_1(E_128))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_561])).
% 3.32/1.58  tff(c_588, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_374, c_582])).
% 3.32/1.58  tff(c_594, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_588])).
% 3.32/1.58  tff(c_279, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_265, c_36])).
% 3.32/1.58  tff(c_373, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_364, c_364, c_364, c_279])).
% 3.32/1.58  tff(c_599, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_594, c_373])).
% 3.32/1.58  tff(c_286, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_277, c_280])).
% 3.32/1.58  tff(c_292, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_286])).
% 3.32/1.58  tff(c_276, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_40])).
% 3.32/1.58  tff(c_319, plain, (![A_92, B_93, C_94]: (k1_relset_1(A_92, B_93, C_94)=k1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.32/1.58  tff(c_327, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_277, c_319])).
% 3.32/1.58  tff(c_26, plain, (![B_18, C_19]: (k1_relset_1(k1_xboole_0, B_18, C_19)=k1_xboole_0 | ~v1_funct_2(C_19, k1_xboole_0, B_18) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.32/1.58  tff(c_352, plain, (![B_97, C_98]: (k1_relset_1('#skF_3', B_97, C_98)='#skF_3' | ~v1_funct_2(C_98, '#skF_3', B_97) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_97))))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_260, c_260, c_260, c_26])).
% 3.32/1.58  tff(c_355, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_277, c_352])).
% 3.32/1.58  tff(c_358, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_276, c_327, c_355])).
% 3.32/1.58  tff(c_365, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_364, c_358])).
% 3.32/1.58  tff(c_530, plain, (![B_112, A_113]: (v2_funct_1(B_112) | ~r1_tarski(k2_relat_1(B_112), k1_relat_1(A_113)) | ~v2_funct_1(k5_relat_1(B_112, A_113)) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.32/1.58  tff(c_536, plain, (![B_112]: (v2_funct_1(B_112) | ~r1_tarski(k2_relat_1(B_112), '#skF_1') | ~v2_funct_1(k5_relat_1(B_112, '#skF_5')) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_365, c_530])).
% 3.32/1.58  tff(c_546, plain, (![B_114]: (v2_funct_1(B_114) | ~r1_tarski(k2_relat_1(B_114), '#skF_1') | ~v2_funct_1(k5_relat_1(B_114, '#skF_5')) | ~v1_funct_1(B_114) | ~v1_relat_1(B_114))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_42, c_536])).
% 3.32/1.58  tff(c_551, plain, (![B_5]: (v2_funct_1(B_5) | ~v2_funct_1(k5_relat_1(B_5, '#skF_5')) | ~v1_funct_1(B_5) | ~v5_relat_1(B_5, '#skF_1') | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_546])).
% 3.32/1.58  tff(c_606, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_599, c_551])).
% 3.32/1.58  tff(c_609, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_289, c_372, c_48, c_606])).
% 3.32/1.58  tff(c_611, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_609])).
% 3.32/1.58  tff(c_612, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_346])).
% 3.32/1.58  tff(c_621, plain, (v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_612, c_300])).
% 3.32/1.58  tff(c_623, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_612, c_278])).
% 3.32/1.58  tff(c_624, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_612, c_612, c_277])).
% 3.32/1.58  tff(c_778, plain, (![E_149, D_148, B_147, A_150, F_151, C_146]: (k1_partfun1(A_150, B_147, C_146, D_148, E_149, F_151)=k5_relat_1(E_149, F_151) | ~m1_subset_1(F_151, k1_zfmisc_1(k2_zfmisc_1(C_146, D_148))) | ~v1_funct_1(F_151) | ~m1_subset_1(E_149, k1_zfmisc_1(k2_zfmisc_1(A_150, B_147))) | ~v1_funct_1(E_149))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.32/1.58  tff(c_782, plain, (![A_150, B_147, E_149]: (k1_partfun1(A_150, B_147, '#skF_4', '#skF_4', E_149, '#skF_5')=k5_relat_1(E_149, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_149, k1_zfmisc_1(k2_zfmisc_1(A_150, B_147))) | ~v1_funct_1(E_149))), inference(resolution, [status(thm)], [c_624, c_778])).
% 3.32/1.58  tff(c_823, plain, (![A_159, B_160, E_161]: (k1_partfun1(A_159, B_160, '#skF_4', '#skF_4', E_161, '#skF_5')=k5_relat_1(E_161, '#skF_5') | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))) | ~v1_funct_1(E_161))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_782])).
% 3.32/1.58  tff(c_826, plain, (k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_623, c_823])).
% 3.32/1.58  tff(c_832, plain, (k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_826])).
% 3.32/1.58  tff(c_622, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_612, c_612, c_612, c_279])).
% 3.32/1.58  tff(c_836, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_832, c_622])).
% 3.32/1.58  tff(c_614, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_612, c_358])).
% 3.32/1.58  tff(c_767, plain, (![B_144, A_145]: (v2_funct_1(B_144) | ~r1_tarski(k2_relat_1(B_144), k1_relat_1(A_145)) | ~v2_funct_1(k5_relat_1(B_144, A_145)) | ~v1_funct_1(B_144) | ~v1_relat_1(B_144) | ~v1_funct_1(A_145) | ~v1_relat_1(A_145))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.32/1.58  tff(c_770, plain, (![B_144]: (v2_funct_1(B_144) | ~r1_tarski(k2_relat_1(B_144), '#skF_4') | ~v2_funct_1(k5_relat_1(B_144, '#skF_5')) | ~v1_funct_1(B_144) | ~v1_relat_1(B_144) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_614, c_767])).
% 3.32/1.58  tff(c_789, plain, (![B_152]: (v2_funct_1(B_152) | ~r1_tarski(k2_relat_1(B_152), '#skF_4') | ~v2_funct_1(k5_relat_1(B_152, '#skF_5')) | ~v1_funct_1(B_152) | ~v1_relat_1(B_152))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_42, c_770])).
% 3.32/1.58  tff(c_794, plain, (![B_5]: (v2_funct_1(B_5) | ~v2_funct_1(k5_relat_1(B_5, '#skF_5')) | ~v1_funct_1(B_5) | ~v5_relat_1(B_5, '#skF_4') | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_789])).
% 3.32/1.58  tff(c_843, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_836, c_794])).
% 3.32/1.58  tff(c_846, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_289, c_621, c_48, c_843])).
% 3.32/1.58  tff(c_848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_846])).
% 3.32/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.58  
% 3.32/1.58  Inference rules
% 3.32/1.58  ----------------------
% 3.32/1.58  #Ref     : 0
% 3.32/1.58  #Sup     : 167
% 3.32/1.58  #Fact    : 0
% 3.32/1.58  #Define  : 0
% 3.32/1.58  #Split   : 3
% 3.32/1.58  #Chain   : 0
% 3.32/1.58  #Close   : 0
% 3.32/1.58  
% 3.32/1.58  Ordering : KBO
% 3.32/1.58  
% 3.32/1.58  Simplification rules
% 3.32/1.58  ----------------------
% 3.32/1.58  #Subsume      : 5
% 3.32/1.58  #Demod        : 219
% 3.32/1.58  #Tautology    : 109
% 3.32/1.58  #SimpNegUnit  : 7
% 3.32/1.58  #BackRed      : 39
% 3.32/1.58  
% 3.32/1.58  #Partial instantiations: 0
% 3.32/1.58  #Strategies tried      : 1
% 3.32/1.58  
% 3.32/1.58  Timing (in seconds)
% 3.32/1.58  ----------------------
% 3.32/1.59  Preprocessing        : 0.37
% 3.32/1.59  Parsing              : 0.18
% 3.32/1.59  CNF conversion       : 0.03
% 3.32/1.59  Main loop            : 0.42
% 3.32/1.59  Inferencing          : 0.15
% 3.32/1.59  Reduction            : 0.14
% 3.32/1.59  Demodulation         : 0.10
% 3.32/1.59  BG Simplification    : 0.02
% 3.32/1.59  Subsumption          : 0.06
% 3.32/1.59  Abstraction          : 0.02
% 3.32/1.59  MUC search           : 0.00
% 3.32/1.59  Cooper               : 0.00
% 3.32/1.59  Total                : 0.84
% 3.32/1.59  Index Insertion      : 0.00
% 3.32/1.59  Index Deletion       : 0.00
% 3.32/1.59  Index Matching       : 0.00
% 3.32/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
