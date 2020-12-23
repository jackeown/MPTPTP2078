%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:44 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 122 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 186 expanded)
%              Number of equality atoms :    6 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k6_relset_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_37,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_43,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_37])).

tff(c_47,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_43])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_8,B_9)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_181,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( k6_relset_1(A_62,B_63,C_64,D_65) = k8_relat_1(C_64,D_65)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_192,plain,(
    ! [C_64] : k6_relset_1('#skF_3','#skF_1',C_64,'#skF_4') = k8_relat_1(C_64,'#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_181])).

tff(c_255,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( m1_subset_1(k6_relset_1(A_80,B_81,C_82,D_83),k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_274,plain,(
    ! [C_64] :
      ( m1_subset_1(k8_relat_1(C_64,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_255])).

tff(c_285,plain,(
    ! [C_84] : m1_subset_1(k8_relat_1(C_84,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_274])).

tff(c_16,plain,(
    ! [A_17,B_18,C_19] :
      ( k1_relset_1(A_17,B_18,C_19) = k1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_305,plain,(
    ! [C_84] : k1_relset_1('#skF_3','#skF_1',k8_relat_1(C_84,'#skF_4')) = k1_relat_1(k8_relat_1(C_84,'#skF_4')) ),
    inference(resolution,[status(thm)],[c_285,c_16])).

tff(c_89,plain,(
    ! [A_47,B_48,C_49] :
      ( m1_subset_1(k1_relset_1(A_47,B_48,C_49),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_105,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(k1_relset_1(A_47,B_48,C_49),A_47)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(resolution,[status(thm)],[c_89,c_2])).

tff(c_304,plain,(
    ! [C_84] : r1_tarski(k1_relset_1('#skF_3','#skF_1',k8_relat_1(C_84,'#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_285,c_105])).

tff(c_361,plain,(
    ! [C_84] : r1_tarski(k1_relat_1(k8_relat_1(C_84,'#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_304])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_268,plain,(
    ! [A_80,B_81,C_82,D_83] :
      ( v1_relat_1(k6_relset_1(A_80,B_81,C_82,D_83))
      | ~ v1_relat_1(k2_zfmisc_1(A_80,B_81))
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(resolution,[status(thm)],[c_255,c_6])).

tff(c_310,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( v1_relat_1(k6_relset_1(A_85,B_86,C_87,D_88))
      | ~ m1_subset_1(D_88,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_268])).

tff(c_324,plain,(
    ! [C_87] : v1_relat_1(k6_relset_1('#skF_3','#skF_1',C_87,'#skF_4')) ),
    inference(resolution,[status(thm)],[c_24,c_310])).

tff(c_331,plain,(
    ! [C_87] : v1_relat_1(k8_relat_1(C_87,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_324])).

tff(c_208,plain,(
    ! [C_67,A_68,B_69] :
      ( m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ r1_tarski(k2_relat_1(C_67),B_69)
      | ~ r1_tarski(k1_relat_1(C_67),A_68)
      | ~ v1_relat_1(C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_194,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_22])).

tff(c_228,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_208,c_194])).

tff(c_353,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_228])).

tff(c_354,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_353])).

tff(c_383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_354])).

tff(c_384,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_353])).

tff(c_411,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_384])).

tff(c_415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_411])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n001.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 18:03:30 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.34  
% 2.20/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.34  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.20/1.34  
% 2.20/1.34  %Foreground sorts:
% 2.20/1.34  
% 2.20/1.34  
% 2.20/1.34  %Background operators:
% 2.20/1.34  
% 2.20/1.34  
% 2.20/1.34  %Foreground operators:
% 2.20/1.34  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.20/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.20/1.34  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.20/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.20/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.20/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.20/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.34  
% 2.52/1.36  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.52/1.36  tff(f_71, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_relset_1)).
% 2.52/1.36  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.52/1.36  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 2.52/1.36  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.52/1.36  tff(f_50, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k6_relset_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relset_1)).
% 2.52/1.36  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.52/1.36  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.52/1.36  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.52/1.36  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.52/1.36  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.52/1.36  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.52/1.36  tff(c_37, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.52/1.36  tff(c_43, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_37])).
% 2.52/1.36  tff(c_47, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_43])).
% 2.52/1.36  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k2_relat_1(k8_relat_1(A_8, B_9)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.52/1.36  tff(c_181, plain, (![A_62, B_63, C_64, D_65]: (k6_relset_1(A_62, B_63, C_64, D_65)=k8_relat_1(C_64, D_65) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.52/1.36  tff(c_192, plain, (![C_64]: (k6_relset_1('#skF_3', '#skF_1', C_64, '#skF_4')=k8_relat_1(C_64, '#skF_4'))), inference(resolution, [status(thm)], [c_24, c_181])).
% 2.52/1.36  tff(c_255, plain, (![A_80, B_81, C_82, D_83]: (m1_subset_1(k6_relset_1(A_80, B_81, C_82, D_83), k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.52/1.36  tff(c_274, plain, (![C_64]: (m1_subset_1(k8_relat_1(C_64, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_192, c_255])).
% 2.52/1.36  tff(c_285, plain, (![C_84]: (m1_subset_1(k8_relat_1(C_84, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_274])).
% 2.52/1.36  tff(c_16, plain, (![A_17, B_18, C_19]: (k1_relset_1(A_17, B_18, C_19)=k1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.52/1.36  tff(c_305, plain, (![C_84]: (k1_relset_1('#skF_3', '#skF_1', k8_relat_1(C_84, '#skF_4'))=k1_relat_1(k8_relat_1(C_84, '#skF_4')))), inference(resolution, [status(thm)], [c_285, c_16])).
% 2.52/1.36  tff(c_89, plain, (![A_47, B_48, C_49]: (m1_subset_1(k1_relset_1(A_47, B_48, C_49), k1_zfmisc_1(A_47)) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.52/1.36  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.52/1.36  tff(c_105, plain, (![A_47, B_48, C_49]: (r1_tarski(k1_relset_1(A_47, B_48, C_49), A_47) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(resolution, [status(thm)], [c_89, c_2])).
% 2.52/1.36  tff(c_304, plain, (![C_84]: (r1_tarski(k1_relset_1('#skF_3', '#skF_1', k8_relat_1(C_84, '#skF_4')), '#skF_3'))), inference(resolution, [status(thm)], [c_285, c_105])).
% 2.52/1.36  tff(c_361, plain, (![C_84]: (r1_tarski(k1_relat_1(k8_relat_1(C_84, '#skF_4')), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_305, c_304])).
% 2.52/1.36  tff(c_6, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.52/1.36  tff(c_268, plain, (![A_80, B_81, C_82, D_83]: (v1_relat_1(k6_relset_1(A_80, B_81, C_82, D_83)) | ~v1_relat_1(k2_zfmisc_1(A_80, B_81)) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(resolution, [status(thm)], [c_255, c_6])).
% 2.52/1.36  tff(c_310, plain, (![A_85, B_86, C_87, D_88]: (v1_relat_1(k6_relset_1(A_85, B_86, C_87, D_88)) | ~m1_subset_1(D_88, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_268])).
% 2.52/1.36  tff(c_324, plain, (![C_87]: (v1_relat_1(k6_relset_1('#skF_3', '#skF_1', C_87, '#skF_4')))), inference(resolution, [status(thm)], [c_24, c_310])).
% 2.52/1.36  tff(c_331, plain, (![C_87]: (v1_relat_1(k8_relat_1(C_87, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_324])).
% 2.52/1.36  tff(c_208, plain, (![C_67, A_68, B_69]: (m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~r1_tarski(k2_relat_1(C_67), B_69) | ~r1_tarski(k1_relat_1(C_67), A_68) | ~v1_relat_1(C_67))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.52/1.36  tff(c_22, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.52/1.36  tff(c_194, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_22])).
% 2.52/1.36  tff(c_228, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_208, c_194])).
% 2.52/1.36  tff(c_353, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_331, c_228])).
% 2.52/1.36  tff(c_354, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_353])).
% 2.52/1.36  tff(c_383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_361, c_354])).
% 2.52/1.36  tff(c_384, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_353])).
% 2.52/1.36  tff(c_411, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_384])).
% 2.52/1.36  tff(c_415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_411])).
% 2.52/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.36  
% 2.52/1.36  Inference rules
% 2.52/1.36  ----------------------
% 2.52/1.36  #Ref     : 0
% 2.52/1.36  #Sup     : 83
% 2.52/1.36  #Fact    : 0
% 2.52/1.36  #Define  : 0
% 2.52/1.36  #Split   : 2
% 2.52/1.36  #Chain   : 0
% 2.52/1.36  #Close   : 0
% 2.52/1.36  
% 2.52/1.36  Ordering : KBO
% 2.52/1.36  
% 2.52/1.36  Simplification rules
% 2.52/1.36  ----------------------
% 2.52/1.36  #Subsume      : 9
% 2.52/1.36  #Demod        : 31
% 2.52/1.36  #Tautology    : 16
% 2.52/1.36  #SimpNegUnit  : 0
% 2.52/1.36  #BackRed      : 4
% 2.52/1.36  
% 2.52/1.36  #Partial instantiations: 0
% 2.52/1.36  #Strategies tried      : 1
% 2.52/1.36  
% 2.52/1.36  Timing (in seconds)
% 2.52/1.36  ----------------------
% 2.52/1.36  Preprocessing        : 0.30
% 2.52/1.36  Parsing              : 0.17
% 2.52/1.36  CNF conversion       : 0.02
% 2.52/1.36  Main loop            : 0.26
% 2.52/1.36  Inferencing          : 0.10
% 2.52/1.36  Reduction            : 0.07
% 2.52/1.36  Demodulation         : 0.05
% 2.52/1.36  BG Simplification    : 0.02
% 2.52/1.36  Subsumption          : 0.04
% 2.52/1.36  Abstraction          : 0.02
% 2.52/1.36  MUC search           : 0.00
% 2.52/1.36  Cooper               : 0.00
% 2.52/1.36  Total                : 0.59
% 2.52/1.36  Index Insertion      : 0.00
% 2.52/1.36  Index Deletion       : 0.00
% 2.52/1.36  Index Matching       : 0.00
% 2.52/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
