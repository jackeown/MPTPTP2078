%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:05 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   57 (  87 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 164 expanded)
%              Number of equality atoms :   16 (  33 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_44,plain,(
    ! [B_31,A_32] :
      ( v1_relat_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_47,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_44])).

tff(c_50,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_47])).

tff(c_63,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( k7_relset_1(A_45,B_46,C_47,D_48) = k9_relat_1(C_47,D_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_66,plain,(
    ! [D_48] : k7_relset_1('#skF_3','#skF_4','#skF_5',D_48) = k9_relat_1('#skF_5',D_48) ),
    inference(resolution,[status(thm)],[c_32,c_63])).

tff(c_90,plain,(
    ! [A_59,B_60,C_61] :
      ( k7_relset_1(A_59,B_60,C_61,A_59) = k2_relset_1(A_59,B_60,C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_92,plain,(
    k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_3') = k2_relset_1('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_90])).

tff(c_94,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k9_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_92])).

tff(c_30,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_96,plain,(
    r2_hidden('#skF_2',k9_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_30])).

tff(c_51,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden('#skF_1'(A_33,B_34,C_35),B_34)
      | ~ r2_hidden(A_33,k9_relat_1(C_35,B_34))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_33,B_34,C_35] :
      ( m1_subset_1('#skF_1'(A_33,B_34,C_35),B_34)
      | ~ r2_hidden(A_33,k9_relat_1(C_35,B_34))
      | ~ v1_relat_1(C_35) ) ),
    inference(resolution,[status(thm)],[c_51,c_2])).

tff(c_102,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_55])).

tff(c_108,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_102])).

tff(c_28,plain,(
    ! [E_25] :
      ( k1_funct_1('#skF_5',E_25) != '#skF_2'
      | ~ m1_subset_1(E_25,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_114,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_108,c_28])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_133,plain,(
    ! [A_64,B_65,C_66] :
      ( r2_hidden(k4_tarski('#skF_1'(A_64,B_65,C_66),A_64),C_66)
      | ~ r2_hidden(A_64,k9_relat_1(C_66,B_65))
      | ~ v1_relat_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [C_16,A_14,B_15] :
      ( k1_funct_1(C_16,A_14) = B_15
      | ~ r2_hidden(k4_tarski(A_14,B_15),C_16)
      | ~ v1_funct_1(C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_197,plain,(
    ! [C_72,A_73,B_74] :
      ( k1_funct_1(C_72,'#skF_1'(A_73,B_74,C_72)) = A_73
      | ~ v1_funct_1(C_72)
      | ~ r2_hidden(A_73,k9_relat_1(C_72,B_74))
      | ~ v1_relat_1(C_72) ) ),
    inference(resolution,[status(thm)],[c_133,c_18])).

tff(c_205,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_197])).

tff(c_213,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36,c_205])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.38  
% 2.27/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.38  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.27/1.38  
% 2.27/1.38  %Foreground sorts:
% 2.27/1.38  
% 2.27/1.38  
% 2.27/1.38  %Background operators:
% 2.27/1.38  
% 2.27/1.38  
% 2.27/1.38  %Foreground operators:
% 2.27/1.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.27/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.27/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.27/1.38  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.27/1.38  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.27/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.27/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.27/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.27/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.27/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.38  
% 2.27/1.39  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.27/1.39  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 2.27/1.39  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.27/1.39  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.27/1.39  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.27/1.39  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.27/1.39  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.27/1.39  tff(f_59, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.27/1.39  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.27/1.39  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.27/1.39  tff(c_44, plain, (![B_31, A_32]: (v1_relat_1(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_32)) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.27/1.39  tff(c_47, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_44])).
% 2.27/1.39  tff(c_50, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_47])).
% 2.27/1.39  tff(c_63, plain, (![A_45, B_46, C_47, D_48]: (k7_relset_1(A_45, B_46, C_47, D_48)=k9_relat_1(C_47, D_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.27/1.39  tff(c_66, plain, (![D_48]: (k7_relset_1('#skF_3', '#skF_4', '#skF_5', D_48)=k9_relat_1('#skF_5', D_48))), inference(resolution, [status(thm)], [c_32, c_63])).
% 2.27/1.39  tff(c_90, plain, (![A_59, B_60, C_61]: (k7_relset_1(A_59, B_60, C_61, A_59)=k2_relset_1(A_59, B_60, C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.27/1.39  tff(c_92, plain, (k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_3')=k2_relset_1('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_90])).
% 2.27/1.39  tff(c_94, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k9_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_92])).
% 2.27/1.39  tff(c_30, plain, (r2_hidden('#skF_2', k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.27/1.39  tff(c_96, plain, (r2_hidden('#skF_2', k9_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_30])).
% 2.27/1.39  tff(c_51, plain, (![A_33, B_34, C_35]: (r2_hidden('#skF_1'(A_33, B_34, C_35), B_34) | ~r2_hidden(A_33, k9_relat_1(C_35, B_34)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.27/1.39  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.27/1.39  tff(c_55, plain, (![A_33, B_34, C_35]: (m1_subset_1('#skF_1'(A_33, B_34, C_35), B_34) | ~r2_hidden(A_33, k9_relat_1(C_35, B_34)) | ~v1_relat_1(C_35))), inference(resolution, [status(thm)], [c_51, c_2])).
% 2.27/1.39  tff(c_102, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_55])).
% 2.27/1.39  tff(c_108, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_102])).
% 2.27/1.39  tff(c_28, plain, (![E_25]: (k1_funct_1('#skF_5', E_25)!='#skF_2' | ~m1_subset_1(E_25, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.27/1.39  tff(c_114, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))!='#skF_2'), inference(resolution, [status(thm)], [c_108, c_28])).
% 2.27/1.39  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.27/1.39  tff(c_133, plain, (![A_64, B_65, C_66]: (r2_hidden(k4_tarski('#skF_1'(A_64, B_65, C_66), A_64), C_66) | ~r2_hidden(A_64, k9_relat_1(C_66, B_65)) | ~v1_relat_1(C_66))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.27/1.39  tff(c_18, plain, (![C_16, A_14, B_15]: (k1_funct_1(C_16, A_14)=B_15 | ~r2_hidden(k4_tarski(A_14, B_15), C_16) | ~v1_funct_1(C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.27/1.39  tff(c_197, plain, (![C_72, A_73, B_74]: (k1_funct_1(C_72, '#skF_1'(A_73, B_74, C_72))=A_73 | ~v1_funct_1(C_72) | ~r2_hidden(A_73, k9_relat_1(C_72, B_74)) | ~v1_relat_1(C_72))), inference(resolution, [status(thm)], [c_133, c_18])).
% 2.27/1.39  tff(c_205, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_96, c_197])).
% 2.27/1.39  tff(c_213, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_36, c_205])).
% 2.27/1.39  tff(c_215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_213])).
% 2.27/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.39  
% 2.27/1.39  Inference rules
% 2.27/1.39  ----------------------
% 2.27/1.39  #Ref     : 0
% 2.27/1.39  #Sup     : 39
% 2.27/1.39  #Fact    : 0
% 2.27/1.39  #Define  : 0
% 2.27/1.39  #Split   : 1
% 2.27/1.39  #Chain   : 0
% 2.27/1.39  #Close   : 0
% 2.27/1.39  
% 2.27/1.39  Ordering : KBO
% 2.27/1.39  
% 2.27/1.39  Simplification rules
% 2.27/1.39  ----------------------
% 2.27/1.39  #Subsume      : 2
% 2.27/1.39  #Demod        : 8
% 2.27/1.39  #Tautology    : 9
% 2.27/1.39  #SimpNegUnit  : 1
% 2.27/1.39  #BackRed      : 2
% 2.27/1.39  
% 2.27/1.39  #Partial instantiations: 0
% 2.27/1.39  #Strategies tried      : 1
% 2.27/1.39  
% 2.27/1.39  Timing (in seconds)
% 2.27/1.39  ----------------------
% 2.27/1.39  Preprocessing        : 0.35
% 2.27/1.39  Parsing              : 0.19
% 2.27/1.39  CNF conversion       : 0.02
% 2.27/1.39  Main loop            : 0.19
% 2.27/1.39  Inferencing          : 0.07
% 2.27/1.40  Reduction            : 0.06
% 2.27/1.40  Demodulation         : 0.04
% 2.27/1.40  BG Simplification    : 0.02
% 2.27/1.40  Subsumption          : 0.03
% 2.27/1.40  Abstraction          : 0.02
% 2.27/1.40  MUC search           : 0.00
% 2.27/1.40  Cooper               : 0.00
% 2.27/1.40  Total                : 0.57
% 2.27/1.40  Index Insertion      : 0.00
% 2.27/1.40  Index Deletion       : 0.00
% 2.27/1.40  Index Matching       : 0.00
% 2.27/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
