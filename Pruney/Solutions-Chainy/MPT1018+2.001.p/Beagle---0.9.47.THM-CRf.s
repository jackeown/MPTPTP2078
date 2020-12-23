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
% DateTime   : Thu Dec  3 10:15:45 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 279 expanded)
%              Number of leaves         :   32 ( 117 expanded)
%              Depth                    :   11
%              Number of atoms          :  177 (1046 expanded)
%              Number of equality atoms :   65 ( 290 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(c_32,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_54,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_54])).

tff(c_107,plain,(
    ! [C_41,A_42,B_43] :
      ( v4_relat_1(C_41,A_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_111,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_107])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_284,plain,(
    ! [D_70,C_71,B_72,A_73] :
      ( k1_funct_1(k2_funct_1(D_70),k1_funct_1(D_70,C_71)) = C_71
      | k1_xboole_0 = B_72
      | ~ r2_hidden(C_71,A_73)
      | ~ v2_funct_1(D_70)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72)))
      | ~ v1_funct_2(D_70,A_73,B_72)
      | ~ v1_funct_1(D_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_300,plain,(
    ! [D_74,B_75] :
      ( k1_funct_1(k2_funct_1(D_74),k1_funct_1(D_74,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_75
      | ~ v2_funct_1(D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_75)))
      | ~ v1_funct_2(D_74,'#skF_3',B_75)
      | ~ v1_funct_1(D_74) ) ),
    inference(resolution,[status(thm)],[c_36,c_284])).

tff(c_302,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_300])).

tff(c_305,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_302])).

tff(c_306,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_305])).

tff(c_87,plain,(
    ! [B_36,A_37] :
      ( r1_tarski(k1_relat_1(B_36),A_37)
      | ~ v4_relat_1(B_36,A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_59])).

tff(c_94,plain,(
    ! [B_36] :
      ( k1_relat_1(B_36) = k1_xboole_0
      | ~ v4_relat_1(B_36,k1_xboole_0)
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_87,c_64])).

tff(c_351,plain,(
    ! [B_80] :
      ( k1_relat_1(B_80) = '#skF_3'
      | ~ v4_relat_1(B_80,'#skF_3')
      | ~ v1_relat_1(B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_306,c_94])).

tff(c_354,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_111,c_351])).

tff(c_357,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_354])).

tff(c_38,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_165,plain,(
    ! [D_56,C_57,B_58,A_59] :
      ( k1_funct_1(k2_funct_1(D_56),k1_funct_1(D_56,C_57)) = C_57
      | k1_xboole_0 = B_58
      | ~ r2_hidden(C_57,A_59)
      | ~ v2_funct_1(D_56)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58)))
      | ~ v1_funct_2(D_56,A_59,B_58)
      | ~ v1_funct_1(D_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_178,plain,(
    ! [D_60,B_61] :
      ( k1_funct_1(k2_funct_1(D_60),k1_funct_1(D_60,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_61
      | ~ v2_funct_1(D_60)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_61)))
      | ~ v1_funct_2(D_60,'#skF_3',B_61)
      | ~ v1_funct_1(D_60) ) ),
    inference(resolution,[status(thm)],[c_36,c_165])).

tff(c_180,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_178])).

tff(c_183,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_180])).

tff(c_184,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_229,plain,(
    ! [B_66] :
      ( k1_relat_1(B_66) = '#skF_3'
      | ~ v4_relat_1(B_66,'#skF_3')
      | ~ v1_relat_1(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_184,c_94])).

tff(c_232,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_111,c_229])).

tff(c_235,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_232])).

tff(c_34,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_151,plain,(
    ! [C_53,B_54,A_55] :
      ( C_53 = B_54
      | k1_funct_1(A_55,C_53) != k1_funct_1(A_55,B_54)
      | ~ r2_hidden(C_53,k1_relat_1(A_55))
      | ~ r2_hidden(B_54,k1_relat_1(A_55))
      | ~ v2_funct_1(A_55)
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_157,plain,(
    ! [B_54] :
      ( B_54 = '#skF_5'
      | k1_funct_1('#skF_4',B_54) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_54,k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_151])).

tff(c_161,plain,(
    ! [B_54] :
      ( B_54 = '#skF_5'
      | k1_funct_1('#skF_4',B_54) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_54,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46,c_40,c_157])).

tff(c_164,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_236,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_164])).

tff(c_239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_236])).

tff(c_241,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_240,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_250,plain,(
    ! [D_67,B_68] :
      ( k1_funct_1(k2_funct_1(D_67),k1_funct_1(D_67,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_68
      | ~ v2_funct_1(D_67)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_68)))
      | ~ v1_funct_2(D_67,'#skF_3',B_68)
      | ~ v1_funct_1(D_67) ) ),
    inference(resolution,[status(thm)],[c_38,c_165])).

tff(c_252,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_250])).

tff(c_255,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_240,c_34,c_252])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_32,c_255])).

tff(c_258,plain,(
    ! [B_54] :
      ( B_54 = '#skF_5'
      | k1_funct_1('#skF_4',B_54) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(B_54,k1_relat_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_421,plain,(
    ! [B_84] :
      ( B_84 = '#skF_5'
      | k1_funct_1('#skF_4',B_84) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(B_84,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_258])).

tff(c_424,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_36,c_421])).

tff(c_431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_424])).

tff(c_432,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_305])).

tff(c_433,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_305])).

tff(c_434,plain,(
    ! [D_85,B_86] :
      ( k1_funct_1(k2_funct_1(D_85),k1_funct_1(D_85,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_86
      | ~ v2_funct_1(D_85)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_86)))
      | ~ v1_funct_2(D_85,'#skF_3',B_86)
      | ~ v1_funct_1(D_85) ) ),
    inference(resolution,[status(thm)],[c_38,c_284])).

tff(c_436,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_434])).

tff(c_439,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_34,c_436])).

tff(c_440,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_433,c_439])).

tff(c_449,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_440])).

tff(c_450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:54:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.41  
% 2.58/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.58/1.41  
% 2.58/1.41  %Foreground sorts:
% 2.58/1.41  
% 2.58/1.41  
% 2.58/1.41  %Background operators:
% 2.58/1.41  
% 2.58/1.41  
% 2.58/1.41  %Foreground operators:
% 2.58/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.58/1.41  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.58/1.41  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.58/1.41  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.58/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.58/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.58/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.58/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.58/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.58/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.58/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.58/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.58/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.58/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.58/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.58/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.58/1.41  
% 2.84/1.43  tff(f_96, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_2)).
% 2.84/1.43  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.84/1.43  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.84/1.43  tff(f_78, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 2.84/1.43  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.84/1.43  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.84/1.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.84/1.43  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 2.84/1.43  tff(c_32, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.43  tff(c_36, plain, (r2_hidden('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.43  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.43  tff(c_54, plain, (![C_27, A_28, B_29]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.84/1.43  tff(c_58, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_54])).
% 2.84/1.43  tff(c_107, plain, (![C_41, A_42, B_43]: (v4_relat_1(C_41, A_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.84/1.43  tff(c_111, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_107])).
% 2.84/1.43  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.43  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.43  tff(c_40, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.43  tff(c_284, plain, (![D_70, C_71, B_72, A_73]: (k1_funct_1(k2_funct_1(D_70), k1_funct_1(D_70, C_71))=C_71 | k1_xboole_0=B_72 | ~r2_hidden(C_71, A_73) | ~v2_funct_1(D_70) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))) | ~v1_funct_2(D_70, A_73, B_72) | ~v1_funct_1(D_70))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.84/1.43  tff(c_300, plain, (![D_74, B_75]: (k1_funct_1(k2_funct_1(D_74), k1_funct_1(D_74, '#skF_6'))='#skF_6' | k1_xboole_0=B_75 | ~v2_funct_1(D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_75))) | ~v1_funct_2(D_74, '#skF_3', B_75) | ~v1_funct_1(D_74))), inference(resolution, [status(thm)], [c_36, c_284])).
% 2.84/1.43  tff(c_302, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_300])).
% 2.84/1.43  tff(c_305, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_302])).
% 2.84/1.43  tff(c_306, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_305])).
% 2.84/1.43  tff(c_87, plain, (![B_36, A_37]: (r1_tarski(k1_relat_1(B_36), A_37) | ~v4_relat_1(B_36, A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.84/1.43  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.43  tff(c_59, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.43  tff(c_64, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_59])).
% 2.84/1.43  tff(c_94, plain, (![B_36]: (k1_relat_1(B_36)=k1_xboole_0 | ~v4_relat_1(B_36, k1_xboole_0) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_87, c_64])).
% 2.84/1.43  tff(c_351, plain, (![B_80]: (k1_relat_1(B_80)='#skF_3' | ~v4_relat_1(B_80, '#skF_3') | ~v1_relat_1(B_80))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_306, c_94])).
% 2.84/1.43  tff(c_354, plain, (k1_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_111, c_351])).
% 2.84/1.43  tff(c_357, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_354])).
% 2.84/1.43  tff(c_38, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.43  tff(c_165, plain, (![D_56, C_57, B_58, A_59]: (k1_funct_1(k2_funct_1(D_56), k1_funct_1(D_56, C_57))=C_57 | k1_xboole_0=B_58 | ~r2_hidden(C_57, A_59) | ~v2_funct_1(D_56) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))) | ~v1_funct_2(D_56, A_59, B_58) | ~v1_funct_1(D_56))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.84/1.43  tff(c_178, plain, (![D_60, B_61]: (k1_funct_1(k2_funct_1(D_60), k1_funct_1(D_60, '#skF_6'))='#skF_6' | k1_xboole_0=B_61 | ~v2_funct_1(D_60) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_61))) | ~v1_funct_2(D_60, '#skF_3', B_61) | ~v1_funct_1(D_60))), inference(resolution, [status(thm)], [c_36, c_165])).
% 2.84/1.43  tff(c_180, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_178])).
% 2.84/1.43  tff(c_183, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_180])).
% 2.84/1.43  tff(c_184, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_183])).
% 2.84/1.43  tff(c_229, plain, (![B_66]: (k1_relat_1(B_66)='#skF_3' | ~v4_relat_1(B_66, '#skF_3') | ~v1_relat_1(B_66))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_184, c_94])).
% 2.84/1.43  tff(c_232, plain, (k1_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_111, c_229])).
% 2.84/1.43  tff(c_235, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_232])).
% 2.84/1.43  tff(c_34, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.84/1.43  tff(c_151, plain, (![C_53, B_54, A_55]: (C_53=B_54 | k1_funct_1(A_55, C_53)!=k1_funct_1(A_55, B_54) | ~r2_hidden(C_53, k1_relat_1(A_55)) | ~r2_hidden(B_54, k1_relat_1(A_55)) | ~v2_funct_1(A_55) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.84/1.43  tff(c_157, plain, (![B_54]: (B_54='#skF_5' | k1_funct_1('#skF_4', B_54)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~r2_hidden(B_54, k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_151])).
% 2.84/1.43  tff(c_161, plain, (![B_54]: (B_54='#skF_5' | k1_funct_1('#skF_4', B_54)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~r2_hidden(B_54, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_46, c_40, c_157])).
% 2.84/1.43  tff(c_164, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_161])).
% 2.84/1.43  tff(c_236, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_164])).
% 2.84/1.43  tff(c_239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_236])).
% 2.84/1.43  tff(c_241, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_183])).
% 2.84/1.43  tff(c_240, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_183])).
% 2.84/1.43  tff(c_250, plain, (![D_67, B_68]: (k1_funct_1(k2_funct_1(D_67), k1_funct_1(D_67, '#skF_5'))='#skF_5' | k1_xboole_0=B_68 | ~v2_funct_1(D_67) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_68))) | ~v1_funct_2(D_67, '#skF_3', B_68) | ~v1_funct_1(D_67))), inference(resolution, [status(thm)], [c_38, c_165])).
% 2.84/1.43  tff(c_252, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_250])).
% 2.84/1.43  tff(c_255, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_240, c_34, c_252])).
% 2.84/1.43  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_241, c_32, c_255])).
% 2.84/1.43  tff(c_258, plain, (![B_54]: (B_54='#skF_5' | k1_funct_1('#skF_4', B_54)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(B_54, k1_relat_1('#skF_4')))), inference(splitRight, [status(thm)], [c_161])).
% 2.84/1.43  tff(c_421, plain, (![B_84]: (B_84='#skF_5' | k1_funct_1('#skF_4', B_84)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(B_84, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_357, c_258])).
% 2.84/1.43  tff(c_424, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_36, c_421])).
% 2.84/1.43  tff(c_431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_424])).
% 2.84/1.43  tff(c_432, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_305])).
% 2.84/1.43  tff(c_433, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_305])).
% 2.84/1.43  tff(c_434, plain, (![D_85, B_86]: (k1_funct_1(k2_funct_1(D_85), k1_funct_1(D_85, '#skF_5'))='#skF_5' | k1_xboole_0=B_86 | ~v2_funct_1(D_85) | ~m1_subset_1(D_85, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_86))) | ~v1_funct_2(D_85, '#skF_3', B_86) | ~v1_funct_1(D_85))), inference(resolution, [status(thm)], [c_38, c_284])).
% 2.84/1.43  tff(c_436, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_434])).
% 2.84/1.43  tff(c_439, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_34, c_436])).
% 2.84/1.43  tff(c_440, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_433, c_439])).
% 2.84/1.43  tff(c_449, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_432, c_440])).
% 2.84/1.43  tff(c_450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_449])).
% 2.84/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.43  
% 2.84/1.43  Inference rules
% 2.84/1.43  ----------------------
% 2.84/1.43  #Ref     : 1
% 2.84/1.43  #Sup     : 79
% 2.84/1.43  #Fact    : 0
% 2.84/1.43  #Define  : 0
% 2.84/1.43  #Split   : 3
% 2.84/1.43  #Chain   : 0
% 2.84/1.43  #Close   : 0
% 2.84/1.43  
% 2.84/1.43  Ordering : KBO
% 2.84/1.43  
% 2.84/1.43  Simplification rules
% 2.84/1.43  ----------------------
% 2.84/1.43  #Subsume      : 10
% 2.84/1.43  #Demod        : 89
% 2.84/1.43  #Tautology    : 41
% 2.84/1.43  #SimpNegUnit  : 4
% 2.84/1.43  #BackRed      : 14
% 2.84/1.43  
% 2.84/1.43  #Partial instantiations: 0
% 2.84/1.43  #Strategies tried      : 1
% 2.84/1.43  
% 2.84/1.43  Timing (in seconds)
% 2.84/1.43  ----------------------
% 2.84/1.43  Preprocessing        : 0.33
% 2.84/1.43  Parsing              : 0.17
% 2.84/1.43  CNF conversion       : 0.02
% 2.84/1.43  Main loop            : 0.29
% 2.84/1.43  Inferencing          : 0.11
% 2.84/1.43  Reduction            : 0.09
% 2.84/1.43  Demodulation         : 0.07
% 2.84/1.43  BG Simplification    : 0.02
% 2.84/1.43  Subsumption          : 0.05
% 2.84/1.43  Abstraction          : 0.01
% 2.84/1.43  MUC search           : 0.00
% 2.84/1.43  Cooper               : 0.00
% 2.84/1.43  Total                : 0.67
% 2.84/1.43  Index Insertion      : 0.00
% 2.84/1.43  Index Deletion       : 0.00
% 2.84/1.43  Index Matching       : 0.00
% 2.84/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
