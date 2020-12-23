%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:35 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 224 expanded)
%              Number of leaves         :   29 (  91 expanded)
%              Depth                    :   14
%              Number of atoms          :  130 ( 602 expanded)
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

tff(f_90,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_48,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_44])).

tff(c_116,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k7_relset_1(A_75,B_76,C_77,D_78) = k9_relat_1(C_77,D_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_119,plain,(
    ! [D_78] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_78) = k9_relat_1('#skF_5',D_78) ),
    inference(resolution,[status(thm)],[c_34,c_116])).

tff(c_32,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_122,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_32])).

tff(c_57,plain,(
    ! [A_50,B_51,C_52] :
      ( r2_hidden('#skF_1'(A_50,B_51,C_52),B_51)
      | ~ r2_hidden(A_50,k9_relat_1(C_52,B_51))
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [F_31] :
      ( k1_funct_1('#skF_5',F_31) != '#skF_6'
      | ~ r2_hidden(F_31,'#skF_4')
      | ~ m1_subset_1(F_31,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_68,plain,(
    ! [A_50,C_52] :
      ( k1_funct_1('#skF_5','#skF_1'(A_50,'#skF_4',C_52)) != '#skF_6'
      | ~ m1_subset_1('#skF_1'(A_50,'#skF_4',C_52),'#skF_2')
      | ~ r2_hidden(A_50,k9_relat_1(C_52,'#skF_4'))
      | ~ v1_relat_1(C_52) ) ),
    inference(resolution,[status(thm)],[c_57,c_30])).

tff(c_134,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_122,c_68])).

tff(c_144,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_134])).

tff(c_194,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_18,plain,(
    ! [A_11,B_12,C_13] :
      ( r2_hidden('#skF_1'(A_11,B_12,C_13),k1_relat_1(C_13))
      | ~ r2_hidden(A_11,k9_relat_1(C_13,B_12))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_196,plain,(
    ! [A_86,B_87,C_88] :
      ( r2_hidden(k4_tarski('#skF_1'(A_86,B_87,C_88),A_86),C_88)
      | ~ r2_hidden(A_86,k9_relat_1(C_88,B_87))
      | ~ v1_relat_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [C_19,A_17,B_18] :
      ( k1_funct_1(C_19,A_17) = B_18
      | ~ r2_hidden(k4_tarski(A_17,B_18),C_19)
      | ~ v1_funct_1(C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_320,plain,(
    ! [C_104,A_105,B_106] :
      ( k1_funct_1(C_104,'#skF_1'(A_105,B_106,C_104)) = A_105
      | ~ v1_funct_1(C_104)
      | ~ r2_hidden(A_105,k9_relat_1(C_104,B_106))
      | ~ v1_relat_1(C_104) ) ),
    inference(resolution,[status(thm)],[c_196,c_22])).

tff(c_330,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_122,c_320])).

tff(c_339,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38,c_330])).

tff(c_151,plain,(
    ! [A_80,C_81] :
      ( r2_hidden(k4_tarski(A_80,k1_funct_1(C_81,A_80)),C_81)
      | ~ r2_hidden(A_80,k1_relat_1(C_81))
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_191,plain,(
    ! [A_80,C_81] :
      ( m1_subset_1(k4_tarski(A_80,k1_funct_1(C_81,A_80)),C_81)
      | ~ r2_hidden(A_80,k1_relat_1(C_81))
      | ~ v1_funct_1(C_81)
      | ~ v1_relat_1(C_81) ) ),
    inference(resolution,[status(thm)],[c_151,c_10])).

tff(c_344,plain,
    ( m1_subset_1(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_191])).

tff(c_351,plain,
    ( m1_subset_1(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38,c_344])).

tff(c_355,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_358,plain,
    ( ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_355])).

tff(c_362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_122,c_358])).

tff(c_364,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_20,plain,(
    ! [A_17,C_19] :
      ( r2_hidden(k4_tarski(A_17,k1_funct_1(C_19,A_17)),C_19)
      | ~ r2_hidden(A_17,k1_relat_1(C_19))
      | ~ v1_funct_1(C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_347,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_20])).

tff(c_353,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38,c_347])).

tff(c_442,plain,(
    r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_353])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_466,plain,(
    ! [A_115] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),A_115)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_115)) ) ),
    inference(resolution,[status(thm)],[c_442,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_580,plain,(
    ! [C_123,D_124] :
      ( r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),C_123)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(C_123,D_124))) ) ),
    inference(resolution,[status(thm)],[c_466,c_6])).

tff(c_584,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_580])).

tff(c_591,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_584,c_10])).

tff(c_597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_591])).

tff(c_598,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_601,plain,(
    ! [A_128,B_129,C_130] :
      ( r2_hidden(k4_tarski('#skF_1'(A_128,B_129,C_130),A_128),C_130)
      | ~ r2_hidden(A_128,k9_relat_1(C_130,B_129))
      | ~ v1_relat_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_696,plain,(
    ! [C_144,A_145,B_146] :
      ( k1_funct_1(C_144,'#skF_1'(A_145,B_146,C_144)) = A_145
      | ~ v1_funct_1(C_144)
      | ~ r2_hidden(A_145,k9_relat_1(C_144,B_146))
      | ~ v1_relat_1(C_144) ) ),
    inference(resolution,[status(thm)],[c_601,c_22])).

tff(c_704,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_122,c_696])).

tff(c_712,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38,c_704])).

tff(c_714,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_598,c_712])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.39  
% 2.88/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.40  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.88/1.40  
% 2.88/1.40  %Foreground sorts:
% 2.88/1.40  
% 2.88/1.40  
% 2.88/1.40  %Background operators:
% 2.88/1.40  
% 2.88/1.40  
% 2.88/1.40  %Foreground operators:
% 2.88/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.88/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.88/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.88/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.88/1.40  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.88/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.88/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.88/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.88/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.88/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.88/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.88/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.88/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.88/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.40  
% 2.88/1.41  tff(f_90, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 2.88/1.41  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.88/1.41  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.88/1.41  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.88/1.41  tff(f_63, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.88/1.41  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.88/1.41  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.88/1.41  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.88/1.41  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.88/1.41  tff(c_44, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.88/1.41  tff(c_48, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_44])).
% 2.88/1.41  tff(c_116, plain, (![A_75, B_76, C_77, D_78]: (k7_relset_1(A_75, B_76, C_77, D_78)=k9_relat_1(C_77, D_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.88/1.41  tff(c_119, plain, (![D_78]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_78)=k9_relat_1('#skF_5', D_78))), inference(resolution, [status(thm)], [c_34, c_116])).
% 2.88/1.41  tff(c_32, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.88/1.41  tff(c_122, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_32])).
% 2.88/1.41  tff(c_57, plain, (![A_50, B_51, C_52]: (r2_hidden('#skF_1'(A_50, B_51, C_52), B_51) | ~r2_hidden(A_50, k9_relat_1(C_52, B_51)) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.88/1.41  tff(c_30, plain, (![F_31]: (k1_funct_1('#skF_5', F_31)!='#skF_6' | ~r2_hidden(F_31, '#skF_4') | ~m1_subset_1(F_31, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.88/1.41  tff(c_68, plain, (![A_50, C_52]: (k1_funct_1('#skF_5', '#skF_1'(A_50, '#skF_4', C_52))!='#skF_6' | ~m1_subset_1('#skF_1'(A_50, '#skF_4', C_52), '#skF_2') | ~r2_hidden(A_50, k9_relat_1(C_52, '#skF_4')) | ~v1_relat_1(C_52))), inference(resolution, [status(thm)], [c_57, c_30])).
% 2.88/1.41  tff(c_134, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_122, c_68])).
% 2.88/1.41  tff(c_144, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_134])).
% 2.88/1.41  tff(c_194, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_144])).
% 2.88/1.41  tff(c_18, plain, (![A_11, B_12, C_13]: (r2_hidden('#skF_1'(A_11, B_12, C_13), k1_relat_1(C_13)) | ~r2_hidden(A_11, k9_relat_1(C_13, B_12)) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.88/1.41  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.88/1.41  tff(c_196, plain, (![A_86, B_87, C_88]: (r2_hidden(k4_tarski('#skF_1'(A_86, B_87, C_88), A_86), C_88) | ~r2_hidden(A_86, k9_relat_1(C_88, B_87)) | ~v1_relat_1(C_88))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.88/1.41  tff(c_22, plain, (![C_19, A_17, B_18]: (k1_funct_1(C_19, A_17)=B_18 | ~r2_hidden(k4_tarski(A_17, B_18), C_19) | ~v1_funct_1(C_19) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.88/1.41  tff(c_320, plain, (![C_104, A_105, B_106]: (k1_funct_1(C_104, '#skF_1'(A_105, B_106, C_104))=A_105 | ~v1_funct_1(C_104) | ~r2_hidden(A_105, k9_relat_1(C_104, B_106)) | ~v1_relat_1(C_104))), inference(resolution, [status(thm)], [c_196, c_22])).
% 2.88/1.41  tff(c_330, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_122, c_320])).
% 2.88/1.41  tff(c_339, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38, c_330])).
% 2.88/1.41  tff(c_151, plain, (![A_80, C_81]: (r2_hidden(k4_tarski(A_80, k1_funct_1(C_81, A_80)), C_81) | ~r2_hidden(A_80, k1_relat_1(C_81)) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.88/1.41  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.88/1.41  tff(c_191, plain, (![A_80, C_81]: (m1_subset_1(k4_tarski(A_80, k1_funct_1(C_81, A_80)), C_81) | ~r2_hidden(A_80, k1_relat_1(C_81)) | ~v1_funct_1(C_81) | ~v1_relat_1(C_81))), inference(resolution, [status(thm)], [c_151, c_10])).
% 2.88/1.41  tff(c_344, plain, (m1_subset_1(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_339, c_191])).
% 2.88/1.41  tff(c_351, plain, (m1_subset_1(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38, c_344])).
% 2.88/1.41  tff(c_355, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_351])).
% 2.88/1.41  tff(c_358, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_355])).
% 2.88/1.41  tff(c_362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_122, c_358])).
% 2.88/1.41  tff(c_364, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_351])).
% 2.88/1.41  tff(c_20, plain, (![A_17, C_19]: (r2_hidden(k4_tarski(A_17, k1_funct_1(C_19, A_17)), C_19) | ~r2_hidden(A_17, k1_relat_1(C_19)) | ~v1_funct_1(C_19) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.88/1.41  tff(c_347, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_339, c_20])).
% 2.88/1.41  tff(c_353, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38, c_347])).
% 2.88/1.41  tff(c_442, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_364, c_353])).
% 2.88/1.41  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.88/1.41  tff(c_466, plain, (![A_115]: (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), A_115) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_115)))), inference(resolution, [status(thm)], [c_442, c_8])).
% 2.88/1.41  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.88/1.41  tff(c_580, plain, (![C_123, D_124]: (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), C_123) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(C_123, D_124))))), inference(resolution, [status(thm)], [c_466, c_6])).
% 2.88/1.41  tff(c_584, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_34, c_580])).
% 2.88/1.41  tff(c_591, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_584, c_10])).
% 2.88/1.41  tff(c_597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_591])).
% 2.88/1.41  tff(c_598, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(splitRight, [status(thm)], [c_144])).
% 2.88/1.41  tff(c_601, plain, (![A_128, B_129, C_130]: (r2_hidden(k4_tarski('#skF_1'(A_128, B_129, C_130), A_128), C_130) | ~r2_hidden(A_128, k9_relat_1(C_130, B_129)) | ~v1_relat_1(C_130))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.88/1.41  tff(c_696, plain, (![C_144, A_145, B_146]: (k1_funct_1(C_144, '#skF_1'(A_145, B_146, C_144))=A_145 | ~v1_funct_1(C_144) | ~r2_hidden(A_145, k9_relat_1(C_144, B_146)) | ~v1_relat_1(C_144))), inference(resolution, [status(thm)], [c_601, c_22])).
% 2.88/1.41  tff(c_704, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_122, c_696])).
% 2.88/1.41  tff(c_712, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38, c_704])).
% 2.88/1.41  tff(c_714, plain, $false, inference(negUnitSimplification, [status(thm)], [c_598, c_712])).
% 2.88/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.41  
% 2.88/1.41  Inference rules
% 2.88/1.41  ----------------------
% 2.88/1.41  #Ref     : 0
% 2.88/1.41  #Sup     : 148
% 2.88/1.41  #Fact    : 0
% 2.88/1.41  #Define  : 0
% 2.88/1.41  #Split   : 3
% 2.88/1.41  #Chain   : 0
% 2.88/1.41  #Close   : 0
% 2.88/1.41  
% 2.88/1.41  Ordering : KBO
% 2.88/1.41  
% 2.88/1.41  Simplification rules
% 2.88/1.41  ----------------------
% 2.88/1.41  #Subsume      : 7
% 2.88/1.41  #Demod        : 26
% 2.88/1.41  #Tautology    : 12
% 2.88/1.41  #SimpNegUnit  : 2
% 2.88/1.41  #BackRed      : 3
% 2.88/1.41  
% 2.88/1.41  #Partial instantiations: 0
% 2.88/1.41  #Strategies tried      : 1
% 2.88/1.41  
% 2.88/1.41  Timing (in seconds)
% 2.88/1.41  ----------------------
% 2.88/1.41  Preprocessing        : 0.30
% 2.88/1.41  Parsing              : 0.16
% 2.88/1.41  CNF conversion       : 0.02
% 2.88/1.41  Main loop            : 0.35
% 2.88/1.41  Inferencing          : 0.13
% 2.88/1.41  Reduction            : 0.09
% 2.88/1.41  Demodulation         : 0.07
% 2.88/1.42  BG Simplification    : 0.02
% 2.88/1.42  Subsumption          : 0.08
% 2.88/1.42  Abstraction          : 0.02
% 2.88/1.42  MUC search           : 0.00
% 2.88/1.42  Cooper               : 0.00
% 2.88/1.42  Total                : 0.68
% 2.88/1.42  Index Insertion      : 0.00
% 2.88/1.42  Index Deletion       : 0.00
% 2.88/1.42  Index Matching       : 0.00
% 2.88/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
