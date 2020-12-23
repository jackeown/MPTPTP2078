%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:29 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 186 expanded)
%              Number of leaves         :   31 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  103 ( 462 expanded)
%              Number of equality atoms :   14 (  62 expanded)
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

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_6,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_38,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_41,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_38])).

tff(c_44,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_41])).

tff(c_107,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( k7_relset_1(A_66,B_67,C_68,D_69) = k9_relat_1(C_68,D_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_114,plain,(
    ! [D_69] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_69) = k9_relat_1('#skF_5',D_69) ),
    inference(resolution,[status(thm)],[c_32,c_107])).

tff(c_30,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_116,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_30])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden('#skF_1'(A_10,B_11,C_12),B_11)
      | ~ r2_hidden(A_10,k9_relat_1(C_12,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_129,plain,(
    ! [A_71,B_72,C_73] :
      ( r2_hidden(k4_tarski('#skF_1'(A_71,B_72,C_73),A_71),C_73)
      | ~ r2_hidden(A_71,k9_relat_1(C_73,B_72))
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [C_18,A_16,B_17] :
      ( k1_funct_1(C_18,A_16) = B_17
      | ~ r2_hidden(k4_tarski(A_16,B_17),C_18)
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_181,plain,(
    ! [C_81,A_82,B_83] :
      ( k1_funct_1(C_81,'#skF_1'(A_82,B_83,C_81)) = A_82
      | ~ v1_funct_1(C_81)
      | ~ r2_hidden(A_82,k9_relat_1(C_81,B_83))
      | ~ v1_relat_1(C_81) ) ),
    inference(resolution,[status(thm)],[c_129,c_18])).

tff(c_189,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_116,c_181])).

tff(c_197,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_189])).

tff(c_51,plain,(
    ! [A_43,B_44,C_45] :
      ( k1_relset_1(A_43,B_44,C_45) = k1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_55,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_51])).

tff(c_70,plain,(
    ! [A_52,B_53,C_54] :
      ( m1_subset_1(k1_relset_1(A_52,B_53,C_54),k1_zfmisc_1(A_52))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_80,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_70])).

tff(c_84,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_80])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden('#skF_1'(A_10,B_11,C_12),k1_relat_1(C_12))
      | ~ r2_hidden(A_10,k9_relat_1(C_12,B_11))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_16,C_18] :
      ( r2_hidden(k4_tarski(A_16,k1_funct_1(C_18,A_16)),C_18)
      | ~ r2_hidden(A_16,k1_relat_1(C_18))
      | ~ v1_funct_1(C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_202,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_16])).

tff(c_206,plain,
    ( r2_hidden(k4_tarski('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_202])).

tff(c_208,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_211,plain,
    ( ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_208])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_116,c_211])).

tff(c_217,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_263,plain,(
    ! [A_88] :
      ( r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),A_88)
      | ~ m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1(A_88)) ) ),
    inference(resolution,[status(thm)],[c_217,c_2])).

tff(c_267,plain,(
    r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_263])).

tff(c_28,plain,(
    ! [F_33] :
      ( k1_funct_1('#skF_5',F_33) != '#skF_6'
      | ~ r2_hidden(F_33,'#skF_4')
      | ~ r2_hidden(F_33,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_274,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6'
    | ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_267,c_28])).

tff(c_279,plain,(
    ~ r2_hidden('#skF_1'('#skF_6','#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_274])).

tff(c_296,plain,
    ( ~ r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_279])).

tff(c_303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_116,c_296])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:23:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.31  
% 2.39/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.31  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.39/1.31  
% 2.39/1.31  %Foreground sorts:
% 2.39/1.31  
% 2.39/1.31  
% 2.39/1.31  %Background operators:
% 2.39/1.31  
% 2.39/1.31  
% 2.39/1.31  %Foreground operators:
% 2.39/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.39/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.39/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.39/1.31  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.39/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.39/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.39/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.39/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.39/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.39/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.39/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.39/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.39/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.39/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.31  
% 2.39/1.33  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.39/1.33  tff(f_93, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 2.39/1.33  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.39/1.33  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.39/1.33  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.39/1.33  tff(f_62, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.39/1.33  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.39/1.33  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.39/1.33  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.39/1.33  tff(c_6, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.39/1.33  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.39/1.33  tff(c_38, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.39/1.33  tff(c_41, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_38])).
% 2.39/1.33  tff(c_44, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_41])).
% 2.39/1.33  tff(c_107, plain, (![A_66, B_67, C_68, D_69]: (k7_relset_1(A_66, B_67, C_68, D_69)=k9_relat_1(C_68, D_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.39/1.33  tff(c_114, plain, (![D_69]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_69)=k9_relat_1('#skF_5', D_69))), inference(resolution, [status(thm)], [c_32, c_107])).
% 2.39/1.33  tff(c_30, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.39/1.33  tff(c_116, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_30])).
% 2.39/1.33  tff(c_10, plain, (![A_10, B_11, C_12]: (r2_hidden('#skF_1'(A_10, B_11, C_12), B_11) | ~r2_hidden(A_10, k9_relat_1(C_12, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.39/1.33  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.39/1.33  tff(c_129, plain, (![A_71, B_72, C_73]: (r2_hidden(k4_tarski('#skF_1'(A_71, B_72, C_73), A_71), C_73) | ~r2_hidden(A_71, k9_relat_1(C_73, B_72)) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.39/1.33  tff(c_18, plain, (![C_18, A_16, B_17]: (k1_funct_1(C_18, A_16)=B_17 | ~r2_hidden(k4_tarski(A_16, B_17), C_18) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.39/1.33  tff(c_181, plain, (![C_81, A_82, B_83]: (k1_funct_1(C_81, '#skF_1'(A_82, B_83, C_81))=A_82 | ~v1_funct_1(C_81) | ~r2_hidden(A_82, k9_relat_1(C_81, B_83)) | ~v1_relat_1(C_81))), inference(resolution, [status(thm)], [c_129, c_18])).
% 2.39/1.33  tff(c_189, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_116, c_181])).
% 2.39/1.33  tff(c_197, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_189])).
% 2.39/1.33  tff(c_51, plain, (![A_43, B_44, C_45]: (k1_relset_1(A_43, B_44, C_45)=k1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.39/1.33  tff(c_55, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_51])).
% 2.39/1.33  tff(c_70, plain, (![A_52, B_53, C_54]: (m1_subset_1(k1_relset_1(A_52, B_53, C_54), k1_zfmisc_1(A_52)) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.39/1.33  tff(c_80, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_55, c_70])).
% 2.39/1.33  tff(c_84, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_80])).
% 2.39/1.33  tff(c_14, plain, (![A_10, B_11, C_12]: (r2_hidden('#skF_1'(A_10, B_11, C_12), k1_relat_1(C_12)) | ~r2_hidden(A_10, k9_relat_1(C_12, B_11)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.39/1.33  tff(c_16, plain, (![A_16, C_18]: (r2_hidden(k4_tarski(A_16, k1_funct_1(C_18, A_16)), C_18) | ~r2_hidden(A_16, k1_relat_1(C_18)) | ~v1_funct_1(C_18) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.39/1.33  tff(c_202, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_197, c_16])).
% 2.39/1.33  tff(c_206, plain, (r2_hidden(k4_tarski('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_6'), '#skF_5') | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_202])).
% 2.39/1.33  tff(c_208, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_206])).
% 2.39/1.33  tff(c_211, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14, c_208])).
% 2.39/1.33  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_116, c_211])).
% 2.39/1.33  tff(c_217, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_206])).
% 2.39/1.33  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.39/1.33  tff(c_263, plain, (![A_88]: (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), A_88) | ~m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1(A_88)))), inference(resolution, [status(thm)], [c_217, c_2])).
% 2.39/1.33  tff(c_267, plain, (r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_84, c_263])).
% 2.39/1.33  tff(c_28, plain, (![F_33]: (k1_funct_1('#skF_5', F_33)!='#skF_6' | ~r2_hidden(F_33, '#skF_4') | ~r2_hidden(F_33, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.39/1.33  tff(c_274, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_267, c_28])).
% 2.39/1.33  tff(c_279, plain, (~r2_hidden('#skF_1'('#skF_6', '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_274])).
% 2.39/1.33  tff(c_296, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_279])).
% 2.39/1.33  tff(c_303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_116, c_296])).
% 2.39/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.33  
% 2.39/1.33  Inference rules
% 2.39/1.33  ----------------------
% 2.39/1.33  #Ref     : 0
% 2.39/1.33  #Sup     : 59
% 2.39/1.33  #Fact    : 0
% 2.39/1.33  #Define  : 0
% 2.39/1.33  #Split   : 2
% 2.39/1.33  #Chain   : 0
% 2.39/1.33  #Close   : 0
% 2.39/1.33  
% 2.39/1.33  Ordering : KBO
% 2.39/1.33  
% 2.39/1.33  Simplification rules
% 2.39/1.33  ----------------------
% 2.39/1.33  #Subsume      : 5
% 2.39/1.33  #Demod        : 22
% 2.39/1.33  #Tautology    : 10
% 2.39/1.33  #SimpNegUnit  : 0
% 2.39/1.33  #BackRed      : 2
% 2.39/1.33  
% 2.39/1.33  #Partial instantiations: 0
% 2.39/1.33  #Strategies tried      : 1
% 2.39/1.33  
% 2.39/1.33  Timing (in seconds)
% 2.39/1.33  ----------------------
% 2.39/1.33  Preprocessing        : 0.32
% 2.39/1.33  Parsing              : 0.18
% 2.39/1.33  CNF conversion       : 0.02
% 2.39/1.33  Main loop            : 0.23
% 2.39/1.33  Inferencing          : 0.09
% 2.39/1.33  Reduction            : 0.06
% 2.39/1.33  Demodulation         : 0.05
% 2.39/1.33  BG Simplification    : 0.02
% 2.39/1.33  Subsumption          : 0.05
% 2.39/1.33  Abstraction          : 0.02
% 2.39/1.33  MUC search           : 0.00
% 2.39/1.33  Cooper               : 0.00
% 2.39/1.33  Total                : 0.59
% 2.39/1.33  Index Insertion      : 0.00
% 2.39/1.33  Index Deletion       : 0.00
% 2.77/1.33  Index Matching       : 0.00
% 2.77/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
