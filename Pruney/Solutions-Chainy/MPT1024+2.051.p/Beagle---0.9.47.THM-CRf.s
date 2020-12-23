%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:28 EST 2020

% Result     : Theorem 7.74s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :   63 (  84 expanded)
%              Number of leaves         :   35 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :   98 ( 184 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_80,plain,(
    ! [B_82,A_83] :
      ( v1_relat_1(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_83))
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_86,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_50,c_80])).

tff(c_90,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_86])).

tff(c_54,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_130,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_relset_1(A_93,B_94,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_139,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_50,c_130])).

tff(c_164,plain,(
    ! [A_101,B_102,C_103] :
      ( m1_subset_1(k1_relset_1(A_101,B_102,C_103),k1_zfmisc_1(A_101))
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_180,plain,
    ( m1_subset_1(k1_relat_1('#skF_9'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_164])).

tff(c_185,plain,(
    m1_subset_1(k1_relat_1('#skF_9'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_180])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_193,plain,(
    r1_tarski(k1_relat_1('#skF_9'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_185,c_8])).

tff(c_18,plain,(
    ! [A_13,B_36,D_51] :
      ( k1_funct_1(A_13,'#skF_5'(A_13,B_36,k9_relat_1(A_13,B_36),D_51)) = D_51
      | ~ r2_hidden(D_51,k9_relat_1(A_13,B_36))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ! [A_13,B_36,D_51] :
      ( r2_hidden('#skF_5'(A_13,B_36,k9_relat_1(A_13,B_36),D_51),B_36)
      | ~ r2_hidden(D_51,k9_relat_1(A_13,B_36))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_539,plain,(
    ! [A_168,B_169,D_170] :
      ( r2_hidden('#skF_5'(A_168,B_169,k9_relat_1(A_168,B_169),D_170),k1_relat_1(A_168))
      | ~ r2_hidden(D_170,k9_relat_1(A_168,B_169))
      | ~ v1_funct_1(A_168)
      | ~ v1_relat_1(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2002,plain,(
    ! [A_439,B_440,D_441,B_442] :
      ( r2_hidden('#skF_5'(A_439,B_440,k9_relat_1(A_439,B_440),D_441),B_442)
      | ~ r1_tarski(k1_relat_1(A_439),B_442)
      | ~ r2_hidden(D_441,k9_relat_1(A_439,B_440))
      | ~ v1_funct_1(A_439)
      | ~ v1_relat_1(A_439) ) ),
    inference(resolution,[status(thm)],[c_539,c_2])).

tff(c_46,plain,(
    ! [F_69] :
      ( k1_funct_1('#skF_9',F_69) != '#skF_10'
      | ~ r2_hidden(F_69,'#skF_8')
      | ~ r2_hidden(F_69,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2075,plain,(
    ! [A_457,B_458,D_459] :
      ( k1_funct_1('#skF_9','#skF_5'(A_457,B_458,k9_relat_1(A_457,B_458),D_459)) != '#skF_10'
      | ~ r2_hidden('#skF_5'(A_457,B_458,k9_relat_1(A_457,B_458),D_459),'#skF_8')
      | ~ r1_tarski(k1_relat_1(A_457),'#skF_6')
      | ~ r2_hidden(D_459,k9_relat_1(A_457,B_458))
      | ~ v1_funct_1(A_457)
      | ~ v1_relat_1(A_457) ) ),
    inference(resolution,[status(thm)],[c_2002,c_46])).

tff(c_6114,plain,(
    ! [A_944,D_945] :
      ( k1_funct_1('#skF_9','#skF_5'(A_944,'#skF_8',k9_relat_1(A_944,'#skF_8'),D_945)) != '#skF_10'
      | ~ r1_tarski(k1_relat_1(A_944),'#skF_6')
      | ~ r2_hidden(D_945,k9_relat_1(A_944,'#skF_8'))
      | ~ v1_funct_1(A_944)
      | ~ v1_relat_1(A_944) ) ),
    inference(resolution,[status(thm)],[c_20,c_2075])).

tff(c_6118,plain,(
    ! [D_51] :
      ( D_51 != '#skF_10'
      | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_6')
      | ~ r2_hidden(D_51,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_51,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6114])).

tff(c_6121,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_54,c_90,c_54,c_193,c_6118])).

tff(c_198,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( k7_relset_1(A_104,B_105,C_106,D_107) = k9_relat_1(C_106,D_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_209,plain,(
    ! [D_107] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_107) = k9_relat_1('#skF_9',D_107) ),
    inference(resolution,[status(thm)],[c_50,c_198])).

tff(c_48,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_212,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_48])).

tff(c_6123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6121,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.74/2.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.74/2.74  
% 7.74/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.74/2.75  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 7.74/2.75  
% 7.74/2.75  %Foreground sorts:
% 7.74/2.75  
% 7.74/2.75  
% 7.74/2.75  %Background operators:
% 7.74/2.75  
% 7.74/2.75  
% 7.74/2.75  %Foreground operators:
% 7.74/2.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.74/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.74/2.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.74/2.75  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.74/2.75  tff('#skF_7', type, '#skF_7': $i).
% 7.74/2.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.74/2.75  tff('#skF_10', type, '#skF_10': $i).
% 7.74/2.75  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.74/2.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.74/2.75  tff('#skF_6', type, '#skF_6': $i).
% 7.74/2.75  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.74/2.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.74/2.75  tff('#skF_9', type, '#skF_9': $i).
% 7.74/2.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.74/2.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.74/2.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.74/2.75  tff('#skF_8', type, '#skF_8': $i).
% 7.74/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.74/2.75  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 7.74/2.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.74/2.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.74/2.75  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.74/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.74/2.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.74/2.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.74/2.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.74/2.75  
% 7.74/2.76  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.74/2.76  tff(f_93, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 7.74/2.76  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.74/2.76  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.74/2.76  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 7.74/2.76  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.74/2.76  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 7.74/2.76  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.74/2.76  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 7.74/2.76  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.74/2.76  tff(c_50, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.74/2.76  tff(c_80, plain, (![B_82, A_83]: (v1_relat_1(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_83)) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.74/2.76  tff(c_86, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_50, c_80])).
% 7.74/2.76  tff(c_90, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_86])).
% 7.74/2.76  tff(c_54, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.74/2.76  tff(c_130, plain, (![A_93, B_94, C_95]: (k1_relset_1(A_93, B_94, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.74/2.76  tff(c_139, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_50, c_130])).
% 7.74/2.76  tff(c_164, plain, (![A_101, B_102, C_103]: (m1_subset_1(k1_relset_1(A_101, B_102, C_103), k1_zfmisc_1(A_101)) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.74/2.76  tff(c_180, plain, (m1_subset_1(k1_relat_1('#skF_9'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_139, c_164])).
% 7.74/2.76  tff(c_185, plain, (m1_subset_1(k1_relat_1('#skF_9'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_180])).
% 7.74/2.76  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.74/2.76  tff(c_193, plain, (r1_tarski(k1_relat_1('#skF_9'), '#skF_6')), inference(resolution, [status(thm)], [c_185, c_8])).
% 7.74/2.76  tff(c_18, plain, (![A_13, B_36, D_51]: (k1_funct_1(A_13, '#skF_5'(A_13, B_36, k9_relat_1(A_13, B_36), D_51))=D_51 | ~r2_hidden(D_51, k9_relat_1(A_13, B_36)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.74/2.76  tff(c_20, plain, (![A_13, B_36, D_51]: (r2_hidden('#skF_5'(A_13, B_36, k9_relat_1(A_13, B_36), D_51), B_36) | ~r2_hidden(D_51, k9_relat_1(A_13, B_36)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.74/2.76  tff(c_539, plain, (![A_168, B_169, D_170]: (r2_hidden('#skF_5'(A_168, B_169, k9_relat_1(A_168, B_169), D_170), k1_relat_1(A_168)) | ~r2_hidden(D_170, k9_relat_1(A_168, B_169)) | ~v1_funct_1(A_168) | ~v1_relat_1(A_168))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.74/2.76  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.74/2.76  tff(c_2002, plain, (![A_439, B_440, D_441, B_442]: (r2_hidden('#skF_5'(A_439, B_440, k9_relat_1(A_439, B_440), D_441), B_442) | ~r1_tarski(k1_relat_1(A_439), B_442) | ~r2_hidden(D_441, k9_relat_1(A_439, B_440)) | ~v1_funct_1(A_439) | ~v1_relat_1(A_439))), inference(resolution, [status(thm)], [c_539, c_2])).
% 7.74/2.76  tff(c_46, plain, (![F_69]: (k1_funct_1('#skF_9', F_69)!='#skF_10' | ~r2_hidden(F_69, '#skF_8') | ~r2_hidden(F_69, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.74/2.76  tff(c_2075, plain, (![A_457, B_458, D_459]: (k1_funct_1('#skF_9', '#skF_5'(A_457, B_458, k9_relat_1(A_457, B_458), D_459))!='#skF_10' | ~r2_hidden('#skF_5'(A_457, B_458, k9_relat_1(A_457, B_458), D_459), '#skF_8') | ~r1_tarski(k1_relat_1(A_457), '#skF_6') | ~r2_hidden(D_459, k9_relat_1(A_457, B_458)) | ~v1_funct_1(A_457) | ~v1_relat_1(A_457))), inference(resolution, [status(thm)], [c_2002, c_46])).
% 7.74/2.76  tff(c_6114, plain, (![A_944, D_945]: (k1_funct_1('#skF_9', '#skF_5'(A_944, '#skF_8', k9_relat_1(A_944, '#skF_8'), D_945))!='#skF_10' | ~r1_tarski(k1_relat_1(A_944), '#skF_6') | ~r2_hidden(D_945, k9_relat_1(A_944, '#skF_8')) | ~v1_funct_1(A_944) | ~v1_relat_1(A_944))), inference(resolution, [status(thm)], [c_20, c_2075])).
% 7.74/2.76  tff(c_6118, plain, (![D_51]: (D_51!='#skF_10' | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_6') | ~r2_hidden(D_51, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_51, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_6114])).
% 7.74/2.76  tff(c_6121, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_54, c_90, c_54, c_193, c_6118])).
% 7.74/2.76  tff(c_198, plain, (![A_104, B_105, C_106, D_107]: (k7_relset_1(A_104, B_105, C_106, D_107)=k9_relat_1(C_106, D_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.74/2.76  tff(c_209, plain, (![D_107]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_107)=k9_relat_1('#skF_9', D_107))), inference(resolution, [status(thm)], [c_50, c_198])).
% 7.74/2.76  tff(c_48, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.74/2.76  tff(c_212, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_48])).
% 7.74/2.76  tff(c_6123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6121, c_212])).
% 7.74/2.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.74/2.76  
% 7.74/2.76  Inference rules
% 7.74/2.76  ----------------------
% 7.74/2.76  #Ref     : 3
% 7.74/2.76  #Sup     : 1434
% 7.74/2.76  #Fact    : 0
% 7.74/2.76  #Define  : 0
% 7.74/2.76  #Split   : 16
% 7.74/2.76  #Chain   : 0
% 7.74/2.76  #Close   : 0
% 7.74/2.76  
% 7.74/2.76  Ordering : KBO
% 7.74/2.76  
% 7.74/2.76  Simplification rules
% 7.74/2.76  ----------------------
% 7.74/2.76  #Subsume      : 393
% 7.74/2.76  #Demod        : 229
% 7.74/2.76  #Tautology    : 138
% 7.74/2.76  #SimpNegUnit  : 1
% 7.74/2.76  #BackRed      : 7
% 7.74/2.76  
% 7.74/2.76  #Partial instantiations: 0
% 7.74/2.76  #Strategies tried      : 1
% 7.74/2.76  
% 7.74/2.76  Timing (in seconds)
% 7.74/2.76  ----------------------
% 7.74/2.76  Preprocessing        : 0.33
% 7.74/2.76  Parsing              : 0.17
% 7.74/2.76  CNF conversion       : 0.03
% 7.74/2.76  Main loop            : 1.68
% 7.74/2.76  Inferencing          : 0.55
% 7.74/2.76  Reduction            : 0.51
% 7.74/2.76  Demodulation         : 0.37
% 7.74/2.76  BG Simplification    : 0.06
% 7.74/2.76  Subsumption          : 0.46
% 7.74/2.76  Abstraction          : 0.08
% 7.74/2.76  MUC search           : 0.00
% 7.74/2.76  Cooper               : 0.00
% 7.74/2.76  Total                : 2.04
% 7.74/2.76  Index Insertion      : 0.00
% 7.74/2.76  Index Deletion       : 0.00
% 7.74/2.76  Index Matching       : 0.00
% 7.74/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
