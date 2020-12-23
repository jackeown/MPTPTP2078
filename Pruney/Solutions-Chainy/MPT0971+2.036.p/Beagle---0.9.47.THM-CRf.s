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
% DateTime   : Thu Dec  3 10:11:34 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 100 expanded)
%              Number of leaves         :   32 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 205 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_6,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_50,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_53,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_50])).

tff(c_56,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_53])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_16,plain,(
    ! [A_16] :
      ( k9_relat_1(A_16,k1_relat_1(A_16)) = k2_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_167,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden(k4_tarski('#skF_1'(A_73,B_74,C_75),A_73),C_75)
      | ~ r2_hidden(A_73,k9_relat_1(C_75,B_74))
      | ~ v1_relat_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    ! [C_19,A_17,B_18] :
      ( k1_funct_1(C_19,A_17) = B_18
      | ~ r2_hidden(k4_tarski(A_17,B_18),C_19)
      | ~ v1_funct_1(C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_189,plain,(
    ! [C_76,A_77,B_78] :
      ( k1_funct_1(C_76,'#skF_1'(A_77,B_78,C_76)) = A_77
      | ~ v1_funct_1(C_76)
      | ~ r2_hidden(A_77,k9_relat_1(C_76,B_78))
      | ~ v1_relat_1(C_76) ) ),
    inference(resolution,[status(thm)],[c_167,c_20])).

tff(c_373,plain,(
    ! [A_104,A_105] :
      ( k1_funct_1(A_104,'#skF_1'(A_105,k1_relat_1(A_104),A_104)) = A_105
      | ~ v1_funct_1(A_104)
      | ~ r2_hidden(A_105,k2_relat_1(A_104))
      | ~ v1_relat_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_189])).

tff(c_77,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_relset_1(A_45,B_46,C_47) = k1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_81,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_77])).

tff(c_103,plain,(
    ! [A_59,B_60,C_61] :
      ( m1_subset_1(k1_relset_1(A_59,B_60,C_61),k1_zfmisc_1(A_59))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_117,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_103])).

tff(c_122,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_117])).

tff(c_128,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden('#skF_1'(A_62,B_63,C_64),k1_relat_1(C_64))
      | ~ r2_hidden(A_62,k9_relat_1(C_64,B_63))
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_222,plain,(
    ! [A_83,B_84,C_85,A_86] :
      ( r2_hidden('#skF_1'(A_83,B_84,C_85),A_86)
      | ~ m1_subset_1(k1_relat_1(C_85),k1_zfmisc_1(A_86))
      | ~ r2_hidden(A_83,k9_relat_1(C_85,B_84))
      | ~ v1_relat_1(C_85) ) ),
    inference(resolution,[status(thm)],[c_128,c_2])).

tff(c_224,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_1'(A_83,B_84,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_83,k9_relat_1('#skF_5',B_84))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_122,c_222])).

tff(c_228,plain,(
    ! [A_87,B_88] :
      ( r2_hidden('#skF_1'(A_87,B_88,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_87,k9_relat_1('#skF_5',B_88)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_224])).

tff(c_30,plain,(
    ! [E_30] :
      ( k1_funct_1('#skF_5',E_30) != '#skF_4'
      | ~ r2_hidden(E_30,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_258,plain,(
    ! [A_93,B_94] :
      ( k1_funct_1('#skF_5','#skF_1'(A_93,B_94,'#skF_5')) != '#skF_4'
      | ~ r2_hidden(A_93,k9_relat_1('#skF_5',B_94)) ) ),
    inference(resolution,[status(thm)],[c_228,c_30])).

tff(c_278,plain,(
    ! [A_93] :
      ( k1_funct_1('#skF_5','#skF_1'(A_93,k1_relat_1('#skF_5'),'#skF_5')) != '#skF_4'
      | ~ r2_hidden(A_93,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_258])).

tff(c_284,plain,(
    ! [A_93] :
      ( k1_funct_1('#skF_5','#skF_1'(A_93,k1_relat_1('#skF_5'),'#skF_5')) != '#skF_4'
      | ~ r2_hidden(A_93,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_278])).

tff(c_380,plain,(
    ! [A_105] :
      ( A_105 != '#skF_4'
      | ~ r2_hidden(A_105,k2_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden(A_105,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_284])).

tff(c_391,plain,(
    ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_38,c_380])).

tff(c_62,plain,(
    ! [A_41,B_42,C_43] :
      ( k2_relset_1(A_41,B_42,C_43) = k2_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_66,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_62])).

tff(c_32,plain,(
    r2_hidden('#skF_4',k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_68,plain,(
    r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_32])).

tff(c_393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:16:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.31  
% 2.23/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.31  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.23/1.31  
% 2.23/1.31  %Foreground sorts:
% 2.23/1.31  
% 2.23/1.31  
% 2.23/1.31  %Background operators:
% 2.23/1.31  
% 2.23/1.31  
% 2.23/1.31  %Foreground operators:
% 2.23/1.31  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.23/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.23/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.23/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.23/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.23/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.23/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.23/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.31  
% 2.56/1.33  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.56/1.33  tff(f_94, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 2.56/1.33  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.56/1.33  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.56/1.33  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.56/1.33  tff(f_66, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.56/1.33  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.56/1.33  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.56/1.33  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.56/1.33  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.56/1.33  tff(c_6, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.56/1.33  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.56/1.33  tff(c_50, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.56/1.33  tff(c_53, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_50])).
% 2.56/1.33  tff(c_56, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_53])).
% 2.56/1.33  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.56/1.33  tff(c_16, plain, (![A_16]: (k9_relat_1(A_16, k1_relat_1(A_16))=k2_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.33  tff(c_167, plain, (![A_73, B_74, C_75]: (r2_hidden(k4_tarski('#skF_1'(A_73, B_74, C_75), A_73), C_75) | ~r2_hidden(A_73, k9_relat_1(C_75, B_74)) | ~v1_relat_1(C_75))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.33  tff(c_20, plain, (![C_19, A_17, B_18]: (k1_funct_1(C_19, A_17)=B_18 | ~r2_hidden(k4_tarski(A_17, B_18), C_19) | ~v1_funct_1(C_19) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.33  tff(c_189, plain, (![C_76, A_77, B_78]: (k1_funct_1(C_76, '#skF_1'(A_77, B_78, C_76))=A_77 | ~v1_funct_1(C_76) | ~r2_hidden(A_77, k9_relat_1(C_76, B_78)) | ~v1_relat_1(C_76))), inference(resolution, [status(thm)], [c_167, c_20])).
% 2.56/1.33  tff(c_373, plain, (![A_104, A_105]: (k1_funct_1(A_104, '#skF_1'(A_105, k1_relat_1(A_104), A_104))=A_105 | ~v1_funct_1(A_104) | ~r2_hidden(A_105, k2_relat_1(A_104)) | ~v1_relat_1(A_104) | ~v1_relat_1(A_104))), inference(superposition, [status(thm), theory('equality')], [c_16, c_189])).
% 2.56/1.33  tff(c_77, plain, (![A_45, B_46, C_47]: (k1_relset_1(A_45, B_46, C_47)=k1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.56/1.33  tff(c_81, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_77])).
% 2.56/1.33  tff(c_103, plain, (![A_59, B_60, C_61]: (m1_subset_1(k1_relset_1(A_59, B_60, C_61), k1_zfmisc_1(A_59)) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.56/1.33  tff(c_117, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_81, c_103])).
% 2.56/1.33  tff(c_122, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_117])).
% 2.56/1.33  tff(c_128, plain, (![A_62, B_63, C_64]: (r2_hidden('#skF_1'(A_62, B_63, C_64), k1_relat_1(C_64)) | ~r2_hidden(A_62, k9_relat_1(C_64, B_63)) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.56/1.33  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.56/1.33  tff(c_222, plain, (![A_83, B_84, C_85, A_86]: (r2_hidden('#skF_1'(A_83, B_84, C_85), A_86) | ~m1_subset_1(k1_relat_1(C_85), k1_zfmisc_1(A_86)) | ~r2_hidden(A_83, k9_relat_1(C_85, B_84)) | ~v1_relat_1(C_85))), inference(resolution, [status(thm)], [c_128, c_2])).
% 2.56/1.33  tff(c_224, plain, (![A_83, B_84]: (r2_hidden('#skF_1'(A_83, B_84, '#skF_5'), '#skF_2') | ~r2_hidden(A_83, k9_relat_1('#skF_5', B_84)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_122, c_222])).
% 2.56/1.33  tff(c_228, plain, (![A_87, B_88]: (r2_hidden('#skF_1'(A_87, B_88, '#skF_5'), '#skF_2') | ~r2_hidden(A_87, k9_relat_1('#skF_5', B_88)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_224])).
% 2.56/1.33  tff(c_30, plain, (![E_30]: (k1_funct_1('#skF_5', E_30)!='#skF_4' | ~r2_hidden(E_30, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.56/1.33  tff(c_258, plain, (![A_93, B_94]: (k1_funct_1('#skF_5', '#skF_1'(A_93, B_94, '#skF_5'))!='#skF_4' | ~r2_hidden(A_93, k9_relat_1('#skF_5', B_94)))), inference(resolution, [status(thm)], [c_228, c_30])).
% 2.56/1.33  tff(c_278, plain, (![A_93]: (k1_funct_1('#skF_5', '#skF_1'(A_93, k1_relat_1('#skF_5'), '#skF_5'))!='#skF_4' | ~r2_hidden(A_93, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_258])).
% 2.56/1.33  tff(c_284, plain, (![A_93]: (k1_funct_1('#skF_5', '#skF_1'(A_93, k1_relat_1('#skF_5'), '#skF_5'))!='#skF_4' | ~r2_hidden(A_93, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_278])).
% 2.56/1.33  tff(c_380, plain, (![A_105]: (A_105!='#skF_4' | ~r2_hidden(A_105, k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~r2_hidden(A_105, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_373, c_284])).
% 2.56/1.33  tff(c_391, plain, (~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_38, c_380])).
% 2.56/1.33  tff(c_62, plain, (![A_41, B_42, C_43]: (k2_relset_1(A_41, B_42, C_43)=k2_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.56/1.33  tff(c_66, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_62])).
% 2.56/1.33  tff(c_32, plain, (r2_hidden('#skF_4', k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.56/1.33  tff(c_68, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_32])).
% 2.56/1.33  tff(c_393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_391, c_68])).
% 2.56/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.33  
% 2.56/1.33  Inference rules
% 2.56/1.33  ----------------------
% 2.56/1.33  #Ref     : 0
% 2.56/1.33  #Sup     : 78
% 2.56/1.33  #Fact    : 0
% 2.56/1.33  #Define  : 0
% 2.56/1.33  #Split   : 2
% 2.56/1.33  #Chain   : 0
% 2.56/1.33  #Close   : 0
% 2.56/1.33  
% 2.56/1.33  Ordering : KBO
% 2.56/1.33  
% 2.56/1.33  Simplification rules
% 2.56/1.33  ----------------------
% 2.56/1.33  #Subsume      : 6
% 2.56/1.33  #Demod        : 11
% 2.56/1.33  #Tautology    : 10
% 2.56/1.33  #SimpNegUnit  : 1
% 2.56/1.33  #BackRed      : 3
% 2.56/1.33  
% 2.56/1.33  #Partial instantiations: 0
% 2.56/1.33  #Strategies tried      : 1
% 2.56/1.33  
% 2.56/1.33  Timing (in seconds)
% 2.56/1.33  ----------------------
% 2.56/1.33  Preprocessing        : 0.32
% 2.56/1.33  Parsing              : 0.17
% 2.56/1.33  CNF conversion       : 0.02
% 2.56/1.33  Main loop            : 0.25
% 2.56/1.33  Inferencing          : 0.09
% 2.56/1.33  Reduction            : 0.07
% 2.56/1.33  Demodulation         : 0.05
% 2.56/1.33  BG Simplification    : 0.02
% 2.56/1.33  Subsumption          : 0.05
% 2.56/1.33  Abstraction          : 0.02
% 2.56/1.33  MUC search           : 0.00
% 2.56/1.33  Cooper               : 0.00
% 2.56/1.33  Total                : 0.60
% 2.56/1.33  Index Insertion      : 0.00
% 2.56/1.33  Index Deletion       : 0.00
% 2.56/1.33  Index Matching       : 0.00
% 2.56/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
