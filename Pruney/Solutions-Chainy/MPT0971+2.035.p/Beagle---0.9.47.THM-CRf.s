%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:34 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   57 (  85 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   93 ( 181 expanded)
%              Number of equality atoms :   11 (  22 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
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

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
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

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

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

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_12,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_51,plain,(
    ! [B_65,A_66] :
      ( v1_relat_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_44,c_51])).

tff(c_57,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_54])).

tff(c_48,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_16,plain,(
    ! [A_14,C_50] :
      ( k1_funct_1(A_14,'#skF_4'(A_14,k2_relat_1(A_14),C_50)) = C_50
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    ! [A_14,C_50] :
      ( r2_hidden('#skF_4'(A_14,k2_relat_1(A_14),C_50),k1_relat_1(A_14))
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_110,plain,(
    ! [A_95,C_96] :
      ( r2_hidden(k4_tarski(A_95,k1_funct_1(C_96,A_95)),C_96)
      | ~ r2_hidden(A_95,k1_relat_1(C_96))
      | ~ v1_funct_1(C_96)
      | ~ v1_relat_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_360,plain,(
    ! [A_134,C_135,A_136] :
      ( r2_hidden(k4_tarski(A_134,k1_funct_1(C_135,A_134)),A_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(A_136))
      | ~ r2_hidden(A_134,k1_relat_1(C_135))
      | ~ v1_funct_1(C_135)
      | ~ v1_relat_1(C_135) ) ),
    inference(resolution,[status(thm)],[c_110,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_413,plain,(
    ! [A_139,C_140,C_141,D_142] :
      ( r2_hidden(A_139,C_140)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(C_140,D_142)))
      | ~ r2_hidden(A_139,k1_relat_1(C_141))
      | ~ v1_funct_1(C_141)
      | ~ v1_relat_1(C_141) ) ),
    inference(resolution,[status(thm)],[c_360,c_6])).

tff(c_415,plain,(
    ! [A_139] :
      ( r2_hidden(A_139,'#skF_5')
      | ~ r2_hidden(A_139,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_44,c_413])).

tff(c_419,plain,(
    ! [A_143] :
      ( r2_hidden(A_143,'#skF_5')
      | ~ r2_hidden(A_143,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_48,c_415])).

tff(c_447,plain,(
    ! [C_50] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_50),'#skF_5')
      | ~ r2_hidden(C_50,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_18,c_419])).

tff(c_464,plain,(
    ! [C_144] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_144),'#skF_5')
      | ~ r2_hidden(C_144,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_48,c_447])).

tff(c_40,plain,(
    ! [E_61] :
      ( k1_funct_1('#skF_8',E_61) != '#skF_7'
      | ~ r2_hidden(E_61,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_475,plain,(
    ! [C_145] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_145)) != '#skF_7'
      | ~ r2_hidden(C_145,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_464,c_40])).

tff(c_479,plain,(
    ! [C_50] :
      ( C_50 != '#skF_7'
      | ~ r2_hidden(C_50,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_50,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_475])).

tff(c_482,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_48,c_479])).

tff(c_65,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_69,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_65])).

tff(c_42,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_71,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_42])).

tff(c_484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_482,c_71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:59:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.44  
% 2.47/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.44  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.47/1.44  
% 2.47/1.44  %Foreground sorts:
% 2.47/1.44  
% 2.47/1.44  
% 2.47/1.44  %Background operators:
% 2.47/1.44  
% 2.47/1.44  
% 2.47/1.44  %Foreground operators:
% 2.47/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.47/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.47/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.47/1.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.47/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.47/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.47/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.47/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.47/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.47/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.47/1.44  tff('#skF_8', type, '#skF_8': $i).
% 2.47/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.47/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.47/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.47/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.44  
% 2.47/1.46  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.47/1.46  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 2.47/1.46  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.47/1.46  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.47/1.46  tff(f_72, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.47/1.46  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.47/1.46  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.47/1.46  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.47/1.46  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.47/1.46  tff(c_44, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.47/1.46  tff(c_51, plain, (![B_65, A_66]: (v1_relat_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.47/1.46  tff(c_54, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_44, c_51])).
% 2.47/1.46  tff(c_57, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_54])).
% 2.47/1.46  tff(c_48, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.47/1.46  tff(c_16, plain, (![A_14, C_50]: (k1_funct_1(A_14, '#skF_4'(A_14, k2_relat_1(A_14), C_50))=C_50 | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.47/1.46  tff(c_18, plain, (![A_14, C_50]: (r2_hidden('#skF_4'(A_14, k2_relat_1(A_14), C_50), k1_relat_1(A_14)) | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.47/1.46  tff(c_110, plain, (![A_95, C_96]: (r2_hidden(k4_tarski(A_95, k1_funct_1(C_96, A_95)), C_96) | ~r2_hidden(A_95, k1_relat_1(C_96)) | ~v1_funct_1(C_96) | ~v1_relat_1(C_96))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.47/1.46  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.47/1.46  tff(c_360, plain, (![A_134, C_135, A_136]: (r2_hidden(k4_tarski(A_134, k1_funct_1(C_135, A_134)), A_136) | ~m1_subset_1(C_135, k1_zfmisc_1(A_136)) | ~r2_hidden(A_134, k1_relat_1(C_135)) | ~v1_funct_1(C_135) | ~v1_relat_1(C_135))), inference(resolution, [status(thm)], [c_110, c_8])).
% 2.47/1.46  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.46  tff(c_413, plain, (![A_139, C_140, C_141, D_142]: (r2_hidden(A_139, C_140) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(C_140, D_142))) | ~r2_hidden(A_139, k1_relat_1(C_141)) | ~v1_funct_1(C_141) | ~v1_relat_1(C_141))), inference(resolution, [status(thm)], [c_360, c_6])).
% 2.47/1.46  tff(c_415, plain, (![A_139]: (r2_hidden(A_139, '#skF_5') | ~r2_hidden(A_139, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_44, c_413])).
% 2.47/1.46  tff(c_419, plain, (![A_143]: (r2_hidden(A_143, '#skF_5') | ~r2_hidden(A_143, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_48, c_415])).
% 2.47/1.46  tff(c_447, plain, (![C_50]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_50), '#skF_5') | ~r2_hidden(C_50, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_18, c_419])).
% 2.47/1.46  tff(c_464, plain, (![C_144]: (r2_hidden('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_144), '#skF_5') | ~r2_hidden(C_144, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_48, c_447])).
% 2.47/1.46  tff(c_40, plain, (![E_61]: (k1_funct_1('#skF_8', E_61)!='#skF_7' | ~r2_hidden(E_61, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.47/1.46  tff(c_475, plain, (![C_145]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_145))!='#skF_7' | ~r2_hidden(C_145, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_464, c_40])).
% 2.47/1.46  tff(c_479, plain, (![C_50]: (C_50!='#skF_7' | ~r2_hidden(C_50, k2_relat_1('#skF_8')) | ~r2_hidden(C_50, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_475])).
% 2.47/1.46  tff(c_482, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_48, c_479])).
% 2.47/1.46  tff(c_65, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.47/1.46  tff(c_69, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_65])).
% 2.47/1.46  tff(c_42, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.47/1.46  tff(c_71, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_42])).
% 2.47/1.46  tff(c_484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_482, c_71])).
% 2.47/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.46  
% 2.47/1.46  Inference rules
% 2.47/1.46  ----------------------
% 2.47/1.46  #Ref     : 0
% 2.47/1.46  #Sup     : 92
% 2.47/1.46  #Fact    : 0
% 2.47/1.46  #Define  : 0
% 2.47/1.46  #Split   : 1
% 2.47/1.46  #Chain   : 0
% 2.47/1.46  #Close   : 0
% 2.47/1.46  
% 2.47/1.46  Ordering : KBO
% 2.47/1.46  
% 2.47/1.46  Simplification rules
% 2.47/1.46  ----------------------
% 2.47/1.46  #Subsume      : 2
% 2.47/1.46  #Demod        : 21
% 2.47/1.46  #Tautology    : 12
% 2.47/1.46  #SimpNegUnit  : 1
% 2.47/1.46  #BackRed      : 3
% 2.47/1.46  
% 2.47/1.46  #Partial instantiations: 0
% 2.47/1.46  #Strategies tried      : 1
% 2.47/1.46  
% 2.47/1.46  Timing (in seconds)
% 2.47/1.46  ----------------------
% 2.47/1.46  Preprocessing        : 0.36
% 2.47/1.46  Parsing              : 0.17
% 2.47/1.46  CNF conversion       : 0.04
% 2.47/1.46  Main loop            : 0.31
% 2.47/1.46  Inferencing          : 0.11
% 2.47/1.46  Reduction            : 0.08
% 2.47/1.46  Demodulation         : 0.06
% 2.47/1.46  BG Simplification    : 0.03
% 2.47/1.46  Subsumption          : 0.07
% 2.47/1.46  Abstraction          : 0.02
% 2.47/1.46  MUC search           : 0.00
% 2.47/1.46  Cooper               : 0.00
% 2.47/1.46  Total                : 0.70
% 2.47/1.46  Index Insertion      : 0.00
% 2.47/1.46  Index Deletion       : 0.00
% 2.47/1.46  Index Matching       : 0.00
% 2.47/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
