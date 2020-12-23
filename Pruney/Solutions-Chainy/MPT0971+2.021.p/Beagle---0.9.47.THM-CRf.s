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
% DateTime   : Thu Dec  3 10:11:32 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 120 expanded)
%              Number of leaves         :   34 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 278 expanded)
%              Number of equality atoms :   11 (  35 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_14,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_61,plain,(
    ! [B_69,A_70] :
      ( v1_relat_1(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_67,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_61])).

tff(c_71,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_67])).

tff(c_84,plain,(
    ! [C_75,A_76,B_77] :
      ( v4_relat_1(C_75,A_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_93,plain,(
    v4_relat_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_84])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_48,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_18,plain,(
    ! [A_14,C_50] :
      ( k1_funct_1(A_14,'#skF_4'(A_14,k2_relat_1(A_14),C_50)) = C_50
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_194,plain,(
    ! [A_115,C_116] :
      ( r2_hidden('#skF_4'(A_115,k2_relat_1(A_115),C_116),k1_relat_1(A_115))
      | ~ r2_hidden(C_116,k2_relat_1(A_115))
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_298,plain,(
    ! [A_134,C_135,A_136] :
      ( r2_hidden('#skF_4'(A_134,k2_relat_1(A_134),C_135),A_136)
      | ~ m1_subset_1(k1_relat_1(A_134),k1_zfmisc_1(A_136))
      | ~ r2_hidden(C_135,k2_relat_1(A_134))
      | ~ v1_funct_1(A_134)
      | ~ v1_relat_1(A_134) ) ),
    inference(resolution,[status(thm)],[c_194,c_2])).

tff(c_40,plain,(
    ! [E_61] :
      ( k1_funct_1('#skF_8',E_61) != '#skF_7'
      | ~ r2_hidden(E_61,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_314,plain,(
    ! [A_141,C_142] :
      ( k1_funct_1('#skF_8','#skF_4'(A_141,k2_relat_1(A_141),C_142)) != '#skF_7'
      | ~ m1_subset_1(k1_relat_1(A_141),k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(C_142,k2_relat_1(A_141))
      | ~ v1_funct_1(A_141)
      | ~ v1_relat_1(A_141) ) ),
    inference(resolution,[status(thm)],[c_298,c_40])).

tff(c_317,plain,(
    ! [C_50] :
      ( C_50 != '#skF_7'
      | ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(C_50,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(C_50,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_314])).

tff(c_319,plain,(
    ! [C_50] :
      ( C_50 != '#skF_7'
      | ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(C_50,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_48,c_71,c_48,c_317])).

tff(c_320,plain,(
    ~ m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_324,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_320])).

tff(c_327,plain,
    ( ~ v4_relat_1('#skF_8','#skF_5')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_12,c_324])).

tff(c_331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_93,c_327])).

tff(c_353,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_149,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_relset_1(A_96,B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_158,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_149])).

tff(c_42,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_161,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_42])).

tff(c_355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:16:46 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.44  
% 2.71/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.71/1.44  
% 2.71/1.44  %Foreground sorts:
% 2.71/1.44  
% 2.71/1.44  
% 2.71/1.44  %Background operators:
% 2.71/1.44  
% 2.71/1.44  
% 2.71/1.44  %Foreground operators:
% 2.71/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.71/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.71/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.71/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.71/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.71/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.71/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.71/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.71/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.71/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.71/1.44  tff('#skF_8', type, '#skF_8': $i).
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.71/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.71/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.71/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.71/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.71/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.44  
% 2.83/1.46  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.83/1.46  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 2.83/1.46  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.83/1.46  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.83/1.46  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.83/1.46  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.83/1.46  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.83/1.46  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.83/1.46  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.83/1.46  tff(c_14, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.83/1.46  tff(c_44, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.83/1.46  tff(c_61, plain, (![B_69, A_70]: (v1_relat_1(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.83/1.46  tff(c_67, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_44, c_61])).
% 2.83/1.46  tff(c_71, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_67])).
% 2.83/1.46  tff(c_84, plain, (![C_75, A_76, B_77]: (v4_relat_1(C_75, A_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.83/1.46  tff(c_93, plain, (v4_relat_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_84])).
% 2.83/1.46  tff(c_12, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(B_11), A_10) | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.46  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.83/1.46  tff(c_48, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.83/1.46  tff(c_18, plain, (![A_14, C_50]: (k1_funct_1(A_14, '#skF_4'(A_14, k2_relat_1(A_14), C_50))=C_50 | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.83/1.46  tff(c_194, plain, (![A_115, C_116]: (r2_hidden('#skF_4'(A_115, k2_relat_1(A_115), C_116), k1_relat_1(A_115)) | ~r2_hidden(C_116, k2_relat_1(A_115)) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.83/1.46  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.46  tff(c_298, plain, (![A_134, C_135, A_136]: (r2_hidden('#skF_4'(A_134, k2_relat_1(A_134), C_135), A_136) | ~m1_subset_1(k1_relat_1(A_134), k1_zfmisc_1(A_136)) | ~r2_hidden(C_135, k2_relat_1(A_134)) | ~v1_funct_1(A_134) | ~v1_relat_1(A_134))), inference(resolution, [status(thm)], [c_194, c_2])).
% 2.83/1.46  tff(c_40, plain, (![E_61]: (k1_funct_1('#skF_8', E_61)!='#skF_7' | ~r2_hidden(E_61, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.83/1.46  tff(c_314, plain, (![A_141, C_142]: (k1_funct_1('#skF_8', '#skF_4'(A_141, k2_relat_1(A_141), C_142))!='#skF_7' | ~m1_subset_1(k1_relat_1(A_141), k1_zfmisc_1('#skF_5')) | ~r2_hidden(C_142, k2_relat_1(A_141)) | ~v1_funct_1(A_141) | ~v1_relat_1(A_141))), inference(resolution, [status(thm)], [c_298, c_40])).
% 2.83/1.46  tff(c_317, plain, (![C_50]: (C_50!='#skF_7' | ~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5')) | ~r2_hidden(C_50, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(C_50, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_314])).
% 2.83/1.46  tff(c_319, plain, (![C_50]: (C_50!='#skF_7' | ~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5')) | ~r2_hidden(C_50, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_48, c_71, c_48, c_317])).
% 2.83/1.46  tff(c_320, plain, (~m1_subset_1(k1_relat_1('#skF_8'), k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_319])).
% 2.83/1.46  tff(c_324, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_5')), inference(resolution, [status(thm)], [c_6, c_320])).
% 2.83/1.46  tff(c_327, plain, (~v4_relat_1('#skF_8', '#skF_5') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_12, c_324])).
% 2.83/1.46  tff(c_331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_93, c_327])).
% 2.83/1.46  tff(c_353, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_319])).
% 2.83/1.46  tff(c_149, plain, (![A_96, B_97, C_98]: (k2_relset_1(A_96, B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.83/1.46  tff(c_158, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_149])).
% 2.83/1.46  tff(c_42, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.83/1.46  tff(c_161, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_42])).
% 2.83/1.46  tff(c_355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_353, c_161])).
% 2.83/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.46  
% 2.83/1.46  Inference rules
% 2.83/1.46  ----------------------
% 2.83/1.46  #Ref     : 0
% 2.83/1.46  #Sup     : 61
% 2.83/1.46  #Fact    : 0
% 2.83/1.46  #Define  : 0
% 2.83/1.46  #Split   : 2
% 2.83/1.46  #Chain   : 0
% 2.83/1.46  #Close   : 0
% 2.83/1.46  
% 2.83/1.46  Ordering : KBO
% 2.83/1.46  
% 2.83/1.46  Simplification rules
% 2.83/1.46  ----------------------
% 2.83/1.46  #Subsume      : 4
% 2.83/1.46  #Demod        : 18
% 2.83/1.46  #Tautology    : 14
% 2.83/1.46  #SimpNegUnit  : 1
% 2.83/1.46  #BackRed      : 4
% 2.83/1.46  
% 2.83/1.46  #Partial instantiations: 0
% 2.83/1.46  #Strategies tried      : 1
% 2.83/1.46  
% 2.83/1.46  Timing (in seconds)
% 2.83/1.46  ----------------------
% 2.83/1.46  Preprocessing        : 0.35
% 2.83/1.46  Parsing              : 0.18
% 2.83/1.46  CNF conversion       : 0.03
% 2.83/1.46  Main loop            : 0.28
% 2.83/1.46  Inferencing          : 0.11
% 2.83/1.46  Reduction            : 0.08
% 2.83/1.46  Demodulation         : 0.05
% 2.83/1.46  BG Simplification    : 0.02
% 2.83/1.46  Subsumption          : 0.06
% 2.83/1.46  Abstraction          : 0.02
% 2.83/1.46  MUC search           : 0.00
% 2.83/1.46  Cooper               : 0.00
% 2.83/1.46  Total                : 0.66
% 2.83/1.46  Index Insertion      : 0.00
% 2.83/1.46  Index Deletion       : 0.00
% 2.83/1.46  Index Matching       : 0.00
% 2.83/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
