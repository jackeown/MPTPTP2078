%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:38 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 221 expanded)
%              Number of leaves         :   32 (  90 expanded)
%              Depth                    :   12
%              Number of atoms          :  130 ( 558 expanded)
%              Number of equality atoms :   20 (  76 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_97,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_8,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_45,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_51,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_48])).

tff(c_124,plain,(
    ! [A_70,B_71,C_72,D_73] :
      ( k7_relset_1(A_70,B_71,C_72,D_73) = k9_relat_1(C_72,D_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_131,plain,(
    ! [D_73] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_73) = k9_relat_1('#skF_5',D_73) ),
    inference(resolution,[status(thm)],[c_34,c_124])).

tff(c_32,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_142,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_32])).

tff(c_67,plain,(
    ! [A_50,B_51,C_52] :
      ( r2_hidden('#skF_1'(A_50,B_51,C_52),B_51)
      | ~ r2_hidden(A_50,k9_relat_1(C_52,B_51))
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ! [F_35] :
      ( k1_funct_1('#skF_5',F_35) != '#skF_6'
      | ~ r2_hidden(F_35,'#skF_4')
      | ~ m1_subset_1(F_35,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_78,plain,(
    ! [A_50,C_52] :
      ( k1_funct_1('#skF_5','#skF_1'(A_50,'#skF_4',C_52)) != '#skF_6'
      | ~ m1_subset_1('#skF_1'(A_50,'#skF_4',C_52),'#skF_2')
      | ~ r2_hidden(A_50,k9_relat_1(C_52,'#skF_4'))
      | ~ v1_relat_1(C_52) ) ),
    inference(resolution,[status(thm)],[c_67,c_30])).

tff(c_156,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_142,c_78])).

tff(c_167,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_156])).

tff(c_172,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_58,plain,(
    ! [A_47,B_48,C_49] :
      ( k1_relset_1(A_47,B_48,C_49) = k1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_62,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_58])).

tff(c_81,plain,(
    ! [A_56,B_57,C_58] :
      ( m1_subset_1(k1_relset_1(A_56,B_57,C_58),k1_zfmisc_1(A_56))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_91,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_81])).

tff(c_95,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_91])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] :
      ( r2_hidden('#skF_1'(A_12,B_13,C_14),k1_relat_1(C_14))
      | ~ r2_hidden(A_12,k9_relat_1(C_14,B_13))
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_174,plain,(
    ! [A_82,B_83,C_84] :
      ( r2_hidden(k4_tarski('#skF_1'(A_82,B_83,C_84),A_82),C_84)
      | ~ r2_hidden(A_82,k9_relat_1(C_84,B_83))
      | ~ v1_relat_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    ! [C_20,A_18,B_19] :
      ( k1_funct_1(C_20,A_18) = B_19
      | ~ r2_hidden(k4_tarski(A_18,B_19),C_20)
      | ~ v1_funct_1(C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_276,plain,(
    ! [C_92,A_93,B_94] :
      ( k1_funct_1(C_92,'#skF_1'(A_93,B_94,C_92)) = A_93
      | ~ v1_funct_1(C_92)
      | ~ r2_hidden(A_93,k9_relat_1(C_92,B_94))
      | ~ v1_relat_1(C_92) ) ),
    inference(resolution,[status(thm)],[c_174,c_20])).

tff(c_284,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_142,c_276])).

tff(c_292,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_38,c_284])).

tff(c_204,plain,(
    ! [A_85,C_86] :
      ( r2_hidden(k4_tarski(A_85,k1_funct_1(C_86,A_85)),C_86)
      | ~ r2_hidden(A_85,k1_relat_1(C_86))
      | ~ v1_funct_1(C_86)
      | ~ v1_relat_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_234,plain,(
    ! [A_85,C_86] :
      ( m1_subset_1(k4_tarski(A_85,k1_funct_1(C_86,A_85)),C_86)
      | ~ r2_hidden(A_85,k1_relat_1(C_86))
      | ~ v1_funct_1(C_86)
      | ~ v1_relat_1(C_86) ) ),
    inference(resolution,[status(thm)],[c_204,c_4])).

tff(c_297,plain,
    ( m1_subset_1(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_234])).

tff(c_304,plain,
    ( m1_subset_1(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_38,c_297])).

tff(c_308,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_311,plain,
    ( ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_308])).

tff(c_315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_142,c_311])).

tff(c_317,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_344,plain,(
    ! [A_99] :
      ( r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),A_99)
      | ~ m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1(A_99)) ) ),
    inference(resolution,[status(thm)],[c_317,c_2])).

tff(c_348,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_95,c_344])).

tff(c_355,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_348,c_4])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_355])).

tff(c_362,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_365,plain,(
    ! [A_103,B_104,C_105] :
      ( r2_hidden(k4_tarski('#skF_1'(A_103,B_104,C_105),A_103),C_105)
      | ~ r2_hidden(A_103,k9_relat_1(C_105,B_104))
      | ~ v1_relat_1(C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_467,plain,(
    ! [C_113,A_114,B_115] :
      ( k1_funct_1(C_113,'#skF_1'(A_114,B_115,C_113)) = A_114
      | ~ v1_funct_1(C_113)
      | ~ r2_hidden(A_114,k9_relat_1(C_113,B_115))
      | ~ v1_relat_1(C_113) ) ),
    inference(resolution,[status(thm)],[c_365,c_20])).

tff(c_475,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_142,c_467])).

tff(c_483,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_38,c_475])).

tff(c_485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_362,c_483])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.40  
% 2.69/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.40  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.69/1.40  
% 2.69/1.40  %Foreground sorts:
% 2.69/1.40  
% 2.69/1.40  
% 2.69/1.40  %Background operators:
% 2.69/1.40  
% 2.69/1.40  
% 2.69/1.40  %Foreground operators:
% 2.69/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.69/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.69/1.40  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.69/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.69/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.69/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.69/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.69/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.40  
% 2.69/1.42  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.69/1.42  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 2.69/1.42  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.69/1.42  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.69/1.42  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.69/1.42  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.69/1.42  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.69/1.42  tff(f_66, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.69/1.42  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.69/1.42  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.69/1.42  tff(c_8, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.42  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.42  tff(c_45, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.69/1.42  tff(c_48, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_45])).
% 2.69/1.42  tff(c_51, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_48])).
% 2.69/1.42  tff(c_124, plain, (![A_70, B_71, C_72, D_73]: (k7_relset_1(A_70, B_71, C_72, D_73)=k9_relat_1(C_72, D_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.69/1.42  tff(c_131, plain, (![D_73]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_73)=k9_relat_1('#skF_5', D_73))), inference(resolution, [status(thm)], [c_34, c_124])).
% 2.69/1.42  tff(c_32, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.42  tff(c_142, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_32])).
% 2.69/1.42  tff(c_67, plain, (![A_50, B_51, C_52]: (r2_hidden('#skF_1'(A_50, B_51, C_52), B_51) | ~r2_hidden(A_50, k9_relat_1(C_52, B_51)) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.69/1.42  tff(c_30, plain, (![F_35]: (k1_funct_1('#skF_5', F_35)!='#skF_6' | ~r2_hidden(F_35, '#skF_4') | ~m1_subset_1(F_35, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.42  tff(c_78, plain, (![A_50, C_52]: (k1_funct_1('#skF_5', '#skF_1'(A_50, '#skF_4', C_52))!='#skF_6' | ~m1_subset_1('#skF_1'(A_50, '#skF_4', C_52), '#skF_2') | ~r2_hidden(A_50, k9_relat_1(C_52, '#skF_4')) | ~v1_relat_1(C_52))), inference(resolution, [status(thm)], [c_67, c_30])).
% 2.69/1.42  tff(c_156, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_142, c_78])).
% 2.69/1.42  tff(c_167, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_156])).
% 2.69/1.42  tff(c_172, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_167])).
% 2.69/1.42  tff(c_58, plain, (![A_47, B_48, C_49]: (k1_relset_1(A_47, B_48, C_49)=k1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.69/1.42  tff(c_62, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_58])).
% 2.69/1.42  tff(c_81, plain, (![A_56, B_57, C_58]: (m1_subset_1(k1_relset_1(A_56, B_57, C_58), k1_zfmisc_1(A_56)) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.69/1.42  tff(c_91, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_62, c_81])).
% 2.69/1.42  tff(c_95, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_91])).
% 2.69/1.42  tff(c_16, plain, (![A_12, B_13, C_14]: (r2_hidden('#skF_1'(A_12, B_13, C_14), k1_relat_1(C_14)) | ~r2_hidden(A_12, k9_relat_1(C_14, B_13)) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.69/1.42  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.69/1.42  tff(c_174, plain, (![A_82, B_83, C_84]: (r2_hidden(k4_tarski('#skF_1'(A_82, B_83, C_84), A_82), C_84) | ~r2_hidden(A_82, k9_relat_1(C_84, B_83)) | ~v1_relat_1(C_84))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.69/1.42  tff(c_20, plain, (![C_20, A_18, B_19]: (k1_funct_1(C_20, A_18)=B_19 | ~r2_hidden(k4_tarski(A_18, B_19), C_20) | ~v1_funct_1(C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.69/1.42  tff(c_276, plain, (![C_92, A_93, B_94]: (k1_funct_1(C_92, '#skF_1'(A_93, B_94, C_92))=A_93 | ~v1_funct_1(C_92) | ~r2_hidden(A_93, k9_relat_1(C_92, B_94)) | ~v1_relat_1(C_92))), inference(resolution, [status(thm)], [c_174, c_20])).
% 2.69/1.42  tff(c_284, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_142, c_276])).
% 2.69/1.42  tff(c_292, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_51, c_38, c_284])).
% 2.69/1.42  tff(c_204, plain, (![A_85, C_86]: (r2_hidden(k4_tarski(A_85, k1_funct_1(C_86, A_85)), C_86) | ~r2_hidden(A_85, k1_relat_1(C_86)) | ~v1_funct_1(C_86) | ~v1_relat_1(C_86))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.69/1.42  tff(c_4, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.69/1.42  tff(c_234, plain, (![A_85, C_86]: (m1_subset_1(k4_tarski(A_85, k1_funct_1(C_86, A_85)), C_86) | ~r2_hidden(A_85, k1_relat_1(C_86)) | ~v1_funct_1(C_86) | ~v1_relat_1(C_86))), inference(resolution, [status(thm)], [c_204, c_4])).
% 2.69/1.42  tff(c_297, plain, (m1_subset_1(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_292, c_234])).
% 2.69/1.42  tff(c_304, plain, (m1_subset_1(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_38, c_297])).
% 2.69/1.42  tff(c_308, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_304])).
% 2.69/1.42  tff(c_311, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_308])).
% 2.69/1.42  tff(c_315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_142, c_311])).
% 2.69/1.42  tff(c_317, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_304])).
% 2.69/1.42  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.69/1.42  tff(c_344, plain, (![A_99]: (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), A_99) | ~m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1(A_99)))), inference(resolution, [status(thm)], [c_317, c_2])).
% 2.69/1.42  tff(c_348, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_95, c_344])).
% 2.69/1.42  tff(c_355, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_348, c_4])).
% 2.69/1.42  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_355])).
% 2.69/1.42  tff(c_362, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(splitRight, [status(thm)], [c_167])).
% 2.69/1.42  tff(c_365, plain, (![A_103, B_104, C_105]: (r2_hidden(k4_tarski('#skF_1'(A_103, B_104, C_105), A_103), C_105) | ~r2_hidden(A_103, k9_relat_1(C_105, B_104)) | ~v1_relat_1(C_105))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.69/1.42  tff(c_467, plain, (![C_113, A_114, B_115]: (k1_funct_1(C_113, '#skF_1'(A_114, B_115, C_113))=A_114 | ~v1_funct_1(C_113) | ~r2_hidden(A_114, k9_relat_1(C_113, B_115)) | ~v1_relat_1(C_113))), inference(resolution, [status(thm)], [c_365, c_20])).
% 2.69/1.42  tff(c_475, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_142, c_467])).
% 2.69/1.42  tff(c_483, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_51, c_38, c_475])).
% 2.69/1.42  tff(c_485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_362, c_483])).
% 2.69/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.42  
% 2.69/1.42  Inference rules
% 2.69/1.42  ----------------------
% 2.69/1.42  #Ref     : 0
% 2.69/1.42  #Sup     : 96
% 2.69/1.42  #Fact    : 0
% 2.69/1.42  #Define  : 0
% 2.69/1.42  #Split   : 5
% 2.69/1.42  #Chain   : 0
% 2.69/1.42  #Close   : 0
% 2.69/1.42  
% 2.69/1.42  Ordering : KBO
% 2.69/1.42  
% 2.69/1.42  Simplification rules
% 2.69/1.42  ----------------------
% 2.69/1.42  #Subsume      : 5
% 2.69/1.42  #Demod        : 19
% 2.69/1.42  #Tautology    : 11
% 2.69/1.42  #SimpNegUnit  : 2
% 2.69/1.42  #BackRed      : 3
% 2.69/1.42  
% 2.69/1.42  #Partial instantiations: 0
% 2.69/1.42  #Strategies tried      : 1
% 2.69/1.42  
% 2.69/1.42  Timing (in seconds)
% 2.69/1.42  ----------------------
% 2.69/1.42  Preprocessing        : 0.33
% 2.69/1.42  Parsing              : 0.17
% 2.69/1.42  CNF conversion       : 0.02
% 2.69/1.42  Main loop            : 0.32
% 2.69/1.42  Inferencing          : 0.12
% 2.69/1.42  Reduction            : 0.09
% 2.69/1.42  Demodulation         : 0.07
% 2.69/1.42  BG Simplification    : 0.02
% 2.69/1.42  Subsumption          : 0.07
% 2.69/1.42  Abstraction          : 0.02
% 2.69/1.43  MUC search           : 0.00
% 2.69/1.43  Cooper               : 0.00
% 2.69/1.43  Total                : 0.69
% 2.69/1.43  Index Insertion      : 0.00
% 2.69/1.43  Index Deletion       : 0.00
% 2.69/1.43  Index Matching       : 0.00
% 2.69/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
