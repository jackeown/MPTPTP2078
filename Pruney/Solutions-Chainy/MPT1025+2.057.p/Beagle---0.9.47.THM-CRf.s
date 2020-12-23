%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:38 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 254 expanded)
%              Number of leaves         :   30 ( 101 expanded)
%              Depth                    :   14
%              Number of atoms          :  136 ( 662 expanded)
%              Number of equality atoms :   17 (  87 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_14,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_47,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_47])).

tff(c_53,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_50])).

tff(c_125,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( k7_relset_1(A_78,B_79,C_80,D_81) = k9_relat_1(C_80,D_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_128,plain,(
    ! [D_81] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_81) = k9_relat_1('#skF_5',D_81) ),
    inference(resolution,[status(thm)],[c_36,c_125])).

tff(c_34,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_131,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_34])).

tff(c_62,plain,(
    ! [A_53,B_54,C_55] :
      ( r2_hidden('#skF_1'(A_53,B_54,C_55),B_54)
      | ~ r2_hidden(A_53,k9_relat_1(C_55,B_54))
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    ! [F_33] :
      ( k1_funct_1('#skF_5',F_33) != '#skF_6'
      | ~ r2_hidden(F_33,'#skF_4')
      | ~ m1_subset_1(F_33,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_73,plain,(
    ! [A_53,C_55] :
      ( k1_funct_1('#skF_5','#skF_1'(A_53,'#skF_4',C_55)) != '#skF_6'
      | ~ m1_subset_1('#skF_1'(A_53,'#skF_4',C_55),'#skF_2')
      | ~ r2_hidden(A_53,k9_relat_1(C_55,'#skF_4'))
      | ~ v1_relat_1(C_55) ) ),
    inference(resolution,[status(thm)],[c_62,c_32])).

tff(c_188,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_131,c_73])).

tff(c_198,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_188])).

tff(c_225,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_22,plain,(
    ! [A_16,B_17,C_18] :
      ( r2_hidden('#skF_1'(A_16,B_17,C_18),k1_relat_1(C_18))
      | ~ r2_hidden(A_16,k9_relat_1(C_18,B_17))
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_226,plain,(
    ! [A_89,B_90,C_91] :
      ( r2_hidden(k4_tarski('#skF_1'(A_89,B_90,C_91),A_89),C_91)
      | ~ r2_hidden(A_89,k9_relat_1(C_91,B_90))
      | ~ v1_relat_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    ! [C_24,A_22,B_23] :
      ( k1_funct_1(C_24,A_22) = B_23
      | ~ r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_384,plain,(
    ! [C_119,A_120,B_121] :
      ( k1_funct_1(C_119,'#skF_1'(A_120,B_121,C_119)) = A_120
      | ~ v1_funct_1(C_119)
      | ~ r2_hidden(A_120,k9_relat_1(C_119,B_121))
      | ~ v1_relat_1(C_119) ) ),
    inference(resolution,[status(thm)],[c_226,c_26])).

tff(c_392,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_131,c_384])).

tff(c_403,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_40,c_392])).

tff(c_141,plain,(
    ! [A_83,C_84] :
      ( r2_hidden(k4_tarski(A_83,k1_funct_1(C_84,A_83)),C_84)
      | ~ r2_hidden(A_83,k1_relat_1(C_84))
      | ~ v1_funct_1(C_84)
      | ~ v1_relat_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_185,plain,(
    ! [A_83,C_84] :
      ( m1_subset_1(k4_tarski(A_83,k1_funct_1(C_84,A_83)),C_84)
      | ~ r2_hidden(A_83,k1_relat_1(C_84))
      | ~ v1_funct_1(C_84)
      | ~ v1_relat_1(C_84) ) ),
    inference(resolution,[status(thm)],[c_141,c_10])).

tff(c_431,plain,
    ( m1_subset_1(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_185])).

tff(c_438,plain,
    ( m1_subset_1(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_40,c_431])).

tff(c_442,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_438])).

tff(c_445,plain,
    ( ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_442])).

tff(c_449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_131,c_445])).

tff(c_451,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_438])).

tff(c_24,plain,(
    ! [A_22,C_24] :
      ( r2_hidden(k4_tarski(A_22,k1_funct_1(C_24,A_22)),C_24)
      | ~ r2_hidden(A_22,k1_relat_1(C_24))
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_434,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_24])).

tff(c_440,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_40,c_434])).

tff(c_488,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_440])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_516,plain,(
    ! [A_134] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),A_134)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_134)) ) ),
    inference(resolution,[status(thm)],[c_488,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_615,plain,(
    ! [C_139,D_140] :
      ( r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),C_139)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(C_139,D_140))) ) ),
    inference(resolution,[status(thm)],[c_516,c_6])).

tff(c_619,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_615])).

tff(c_679,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_619,c_10])).

tff(c_686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_225,c_679])).

tff(c_687,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_691,plain,(
    ! [A_150,B_151,C_152] :
      ( r2_hidden(k4_tarski('#skF_1'(A_150,B_151,C_152),A_150),C_152)
      | ~ r2_hidden(A_150,k9_relat_1(C_152,B_151))
      | ~ v1_relat_1(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_890,plain,(
    ! [C_181,A_182,B_183] :
      ( k1_funct_1(C_181,'#skF_1'(A_182,B_183,C_181)) = A_182
      | ~ v1_funct_1(C_181)
      | ~ r2_hidden(A_182,k9_relat_1(C_181,B_183))
      | ~ v1_relat_1(C_181) ) ),
    inference(resolution,[status(thm)],[c_691,c_26])).

tff(c_898,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_131,c_890])).

tff(c_909,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_40,c_898])).

tff(c_911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_687,c_909])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:27:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.48  
% 3.14/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.48  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.14/1.48  
% 3.14/1.48  %Foreground sorts:
% 3.14/1.48  
% 3.14/1.48  
% 3.14/1.48  %Background operators:
% 3.14/1.48  
% 3.14/1.48  
% 3.14/1.48  %Foreground operators:
% 3.14/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.14/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.14/1.48  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.14/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.14/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.14/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.14/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.14/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.14/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.14/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.14/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.48  
% 3.14/1.50  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.14/1.50  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 3.14/1.50  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.14/1.50  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.14/1.50  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.14/1.50  tff(f_72, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.14/1.50  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.14/1.50  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.14/1.50  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.14/1.50  tff(c_14, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.14/1.50  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.14/1.50  tff(c_47, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.14/1.50  tff(c_50, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_47])).
% 3.14/1.50  tff(c_53, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_50])).
% 3.14/1.50  tff(c_125, plain, (![A_78, B_79, C_80, D_81]: (k7_relset_1(A_78, B_79, C_80, D_81)=k9_relat_1(C_80, D_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.14/1.50  tff(c_128, plain, (![D_81]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_81)=k9_relat_1('#skF_5', D_81))), inference(resolution, [status(thm)], [c_36, c_125])).
% 3.14/1.50  tff(c_34, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.14/1.50  tff(c_131, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_34])).
% 3.14/1.50  tff(c_62, plain, (![A_53, B_54, C_55]: (r2_hidden('#skF_1'(A_53, B_54, C_55), B_54) | ~r2_hidden(A_53, k9_relat_1(C_55, B_54)) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.14/1.50  tff(c_32, plain, (![F_33]: (k1_funct_1('#skF_5', F_33)!='#skF_6' | ~r2_hidden(F_33, '#skF_4') | ~m1_subset_1(F_33, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.14/1.50  tff(c_73, plain, (![A_53, C_55]: (k1_funct_1('#skF_5', '#skF_1'(A_53, '#skF_4', C_55))!='#skF_6' | ~m1_subset_1('#skF_1'(A_53, '#skF_4', C_55), '#skF_2') | ~r2_hidden(A_53, k9_relat_1(C_55, '#skF_4')) | ~v1_relat_1(C_55))), inference(resolution, [status(thm)], [c_62, c_32])).
% 3.14/1.50  tff(c_188, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_131, c_73])).
% 3.14/1.50  tff(c_198, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_188])).
% 3.14/1.50  tff(c_225, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_198])).
% 3.14/1.50  tff(c_22, plain, (![A_16, B_17, C_18]: (r2_hidden('#skF_1'(A_16, B_17, C_18), k1_relat_1(C_18)) | ~r2_hidden(A_16, k9_relat_1(C_18, B_17)) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.14/1.50  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.14/1.50  tff(c_226, plain, (![A_89, B_90, C_91]: (r2_hidden(k4_tarski('#skF_1'(A_89, B_90, C_91), A_89), C_91) | ~r2_hidden(A_89, k9_relat_1(C_91, B_90)) | ~v1_relat_1(C_91))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.14/1.50  tff(c_26, plain, (![C_24, A_22, B_23]: (k1_funct_1(C_24, A_22)=B_23 | ~r2_hidden(k4_tarski(A_22, B_23), C_24) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.14/1.50  tff(c_384, plain, (![C_119, A_120, B_121]: (k1_funct_1(C_119, '#skF_1'(A_120, B_121, C_119))=A_120 | ~v1_funct_1(C_119) | ~r2_hidden(A_120, k9_relat_1(C_119, B_121)) | ~v1_relat_1(C_119))), inference(resolution, [status(thm)], [c_226, c_26])).
% 3.14/1.50  tff(c_392, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_131, c_384])).
% 3.14/1.50  tff(c_403, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_40, c_392])).
% 3.14/1.50  tff(c_141, plain, (![A_83, C_84]: (r2_hidden(k4_tarski(A_83, k1_funct_1(C_84, A_83)), C_84) | ~r2_hidden(A_83, k1_relat_1(C_84)) | ~v1_funct_1(C_84) | ~v1_relat_1(C_84))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.14/1.50  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.14/1.50  tff(c_185, plain, (![A_83, C_84]: (m1_subset_1(k4_tarski(A_83, k1_funct_1(C_84, A_83)), C_84) | ~r2_hidden(A_83, k1_relat_1(C_84)) | ~v1_funct_1(C_84) | ~v1_relat_1(C_84))), inference(resolution, [status(thm)], [c_141, c_10])).
% 3.14/1.50  tff(c_431, plain, (m1_subset_1(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_403, c_185])).
% 3.14/1.50  tff(c_438, plain, (m1_subset_1(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_40, c_431])).
% 3.14/1.50  tff(c_442, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_438])).
% 3.14/1.50  tff(c_445, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_442])).
% 3.14/1.50  tff(c_449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_131, c_445])).
% 3.14/1.50  tff(c_451, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_438])).
% 3.14/1.50  tff(c_24, plain, (![A_22, C_24]: (r2_hidden(k4_tarski(A_22, k1_funct_1(C_24, A_22)), C_24) | ~r2_hidden(A_22, k1_relat_1(C_24)) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.14/1.50  tff(c_434, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_403, c_24])).
% 3.14/1.50  tff(c_440, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_40, c_434])).
% 3.14/1.50  tff(c_488, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_451, c_440])).
% 3.14/1.50  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.14/1.50  tff(c_516, plain, (![A_134]: (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), A_134) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_134)))), inference(resolution, [status(thm)], [c_488, c_8])).
% 3.14/1.50  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.14/1.50  tff(c_615, plain, (![C_139, D_140]: (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), C_139) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(C_139, D_140))))), inference(resolution, [status(thm)], [c_516, c_6])).
% 3.14/1.50  tff(c_619, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_36, c_615])).
% 3.14/1.50  tff(c_679, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_619, c_10])).
% 3.14/1.50  tff(c_686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_225, c_679])).
% 3.14/1.50  tff(c_687, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(splitRight, [status(thm)], [c_198])).
% 3.14/1.50  tff(c_691, plain, (![A_150, B_151, C_152]: (r2_hidden(k4_tarski('#skF_1'(A_150, B_151, C_152), A_150), C_152) | ~r2_hidden(A_150, k9_relat_1(C_152, B_151)) | ~v1_relat_1(C_152))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.14/1.50  tff(c_890, plain, (![C_181, A_182, B_183]: (k1_funct_1(C_181, '#skF_1'(A_182, B_183, C_181))=A_182 | ~v1_funct_1(C_181) | ~r2_hidden(A_182, k9_relat_1(C_181, B_183)) | ~v1_relat_1(C_181))), inference(resolution, [status(thm)], [c_691, c_26])).
% 3.14/1.50  tff(c_898, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_131, c_890])).
% 3.14/1.50  tff(c_909, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_53, c_40, c_898])).
% 3.14/1.50  tff(c_911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_687, c_909])).
% 3.14/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.50  
% 3.14/1.50  Inference rules
% 3.14/1.50  ----------------------
% 3.14/1.50  #Ref     : 0
% 3.14/1.50  #Sup     : 192
% 3.14/1.50  #Fact    : 0
% 3.14/1.50  #Define  : 0
% 3.14/1.50  #Split   : 4
% 3.14/1.50  #Chain   : 0
% 3.14/1.50  #Close   : 0
% 3.14/1.50  
% 3.14/1.50  Ordering : KBO
% 3.14/1.50  
% 3.14/1.50  Simplification rules
% 3.14/1.50  ----------------------
% 3.14/1.50  #Subsume      : 5
% 3.14/1.50  #Demod        : 34
% 3.14/1.50  #Tautology    : 12
% 3.14/1.50  #SimpNegUnit  : 2
% 3.14/1.50  #BackRed      : 3
% 3.14/1.50  
% 3.14/1.50  #Partial instantiations: 0
% 3.14/1.50  #Strategies tried      : 1
% 3.14/1.50  
% 3.14/1.50  Timing (in seconds)
% 3.14/1.50  ----------------------
% 3.14/1.50  Preprocessing        : 0.31
% 3.14/1.50  Parsing              : 0.16
% 3.14/1.50  CNF conversion       : 0.02
% 3.14/1.50  Main loop            : 0.41
% 3.14/1.50  Inferencing          : 0.15
% 3.14/1.50  Reduction            : 0.11
% 3.14/1.50  Demodulation         : 0.08
% 3.14/1.50  BG Simplification    : 0.02
% 3.14/1.50  Subsumption          : 0.09
% 3.14/1.50  Abstraction          : 0.03
% 3.14/1.50  MUC search           : 0.00
% 3.14/1.50  Cooper               : 0.00
% 3.14/1.50  Total                : 0.75
% 3.14/1.50  Index Insertion      : 0.00
% 3.14/1.50  Index Deletion       : 0.00
% 3.14/1.50  Index Matching       : 0.00
% 3.14/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
