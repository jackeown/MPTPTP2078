%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:06 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   39 (  59 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 ( 132 expanded)
%              Number of equality atoms :   12 (  27 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
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

tff(c_14,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_19,B_20,C_21] :
      ( k7_relset_1(A_19,B_20,C_21,A_19) = k2_relset_1(A_19,B_20,C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_3') = k2_relset_1('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_30])).

tff(c_38,plain,(
    ! [B_22,D_24,C_23,E_25,A_26] :
      ( m1_subset_1('#skF_1'(B_22,C_23,D_24,E_25,A_26),A_26)
      | ~ r2_hidden(E_25,k7_relset_1(A_26,B_22,D_24,C_23))
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k2_zfmisc_1(A_26,B_22)))
      | ~ v1_funct_2(D_24,A_26,B_22)
      | ~ v1_funct_1(D_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_40,plain,(
    ! [E_25] :
      ( m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_5',E_25,'#skF_3'),'#skF_3')
      | ~ r2_hidden(E_25,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_38])).

tff(c_43,plain,(
    ! [E_27] :
      ( m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_5',E_27,'#skF_3'),'#skF_3')
      | ~ r2_hidden(E_27,k2_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_40])).

tff(c_47,plain,(
    m1_subset_1('#skF_1'('#skF_4','#skF_3','#skF_5','#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_43])).

tff(c_12,plain,(
    ! [E_14] :
      ( k1_funct_1('#skF_5',E_14) != '#skF_2'
      | ~ m1_subset_1(E_14,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_51,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_3','#skF_5','#skF_2','#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_47,c_12])).

tff(c_68,plain,(
    ! [D_37,B_35,C_36,A_39,E_38] :
      ( k1_funct_1(D_37,'#skF_1'(B_35,C_36,D_37,E_38,A_39)) = E_38
      | ~ r2_hidden(E_38,k7_relset_1(A_39,B_35,D_37,C_36))
      | ~ m1_subset_1(D_37,k1_zfmisc_1(k2_zfmisc_1(A_39,B_35)))
      | ~ v1_funct_2(D_37,A_39,B_35)
      | ~ v1_funct_1(D_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_73,plain,(
    ! [E_38] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_3','#skF_5',E_38,'#skF_3')) = E_38
      | ~ r2_hidden(E_38,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_68])).

tff(c_77,plain,(
    ! [E_40] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_3','#skF_5',E_40,'#skF_3')) = E_40
      | ~ r2_hidden(E_40,k2_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_73])).

tff(c_84,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_3','#skF_5','#skF_2','#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_77])).

tff(c_89,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n009.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 18:14:56 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.13  
% 1.68/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.13  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.68/1.13  
% 1.68/1.13  %Foreground sorts:
% 1.68/1.13  
% 1.68/1.13  
% 1.68/1.13  %Background operators:
% 1.68/1.13  
% 1.68/1.13  
% 1.68/1.13  %Foreground operators:
% 1.68/1.13  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 1.68/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.13  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.68/1.13  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.68/1.13  tff('#skF_5', type, '#skF_5': $i).
% 1.68/1.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.68/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 1.68/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.68/1.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.68/1.13  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.68/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.68/1.13  
% 1.84/1.14  tff(f_65, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 1.84/1.14  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 1.84/1.14  tff(f_49, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 1.84/1.14  tff(c_14, plain, (r2_hidden('#skF_2', k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.84/1.14  tff(c_20, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.84/1.14  tff(c_18, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.84/1.14  tff(c_16, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.84/1.14  tff(c_30, plain, (![A_19, B_20, C_21]: (k7_relset_1(A_19, B_20, C_21, A_19)=k2_relset_1(A_19, B_20, C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.84/1.14  tff(c_33, plain, (k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_3')=k2_relset_1('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_16, c_30])).
% 1.84/1.14  tff(c_38, plain, (![B_22, D_24, C_23, E_25, A_26]: (m1_subset_1('#skF_1'(B_22, C_23, D_24, E_25, A_26), A_26) | ~r2_hidden(E_25, k7_relset_1(A_26, B_22, D_24, C_23)) | ~m1_subset_1(D_24, k1_zfmisc_1(k2_zfmisc_1(A_26, B_22))) | ~v1_funct_2(D_24, A_26, B_22) | ~v1_funct_1(D_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.84/1.14  tff(c_40, plain, (![E_25]: (m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_5', E_25, '#skF_3'), '#skF_3') | ~r2_hidden(E_25, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_33, c_38])).
% 1.84/1.14  tff(c_43, plain, (![E_27]: (m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_5', E_27, '#skF_3'), '#skF_3') | ~r2_hidden(E_27, k2_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_40])).
% 1.84/1.14  tff(c_47, plain, (m1_subset_1('#skF_1'('#skF_4', '#skF_3', '#skF_5', '#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_14, c_43])).
% 1.84/1.14  tff(c_12, plain, (![E_14]: (k1_funct_1('#skF_5', E_14)!='#skF_2' | ~m1_subset_1(E_14, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.84/1.14  tff(c_51, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_3', '#skF_5', '#skF_2', '#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_47, c_12])).
% 1.84/1.14  tff(c_68, plain, (![D_37, B_35, C_36, A_39, E_38]: (k1_funct_1(D_37, '#skF_1'(B_35, C_36, D_37, E_38, A_39))=E_38 | ~r2_hidden(E_38, k7_relset_1(A_39, B_35, D_37, C_36)) | ~m1_subset_1(D_37, k1_zfmisc_1(k2_zfmisc_1(A_39, B_35))) | ~v1_funct_2(D_37, A_39, B_35) | ~v1_funct_1(D_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.84/1.14  tff(c_73, plain, (![E_38]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_3', '#skF_5', E_38, '#skF_3'))=E_38 | ~r2_hidden(E_38, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_33, c_68])).
% 1.84/1.14  tff(c_77, plain, (![E_40]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_3', '#skF_5', E_40, '#skF_3'))=E_40 | ~r2_hidden(E_40, k2_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_73])).
% 1.84/1.14  tff(c_84, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_3', '#skF_5', '#skF_2', '#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_14, c_77])).
% 1.84/1.14  tff(c_89, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_84])).
% 1.84/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.14  
% 1.84/1.14  Inference rules
% 1.84/1.14  ----------------------
% 1.84/1.14  #Ref     : 0
% 1.84/1.14  #Sup     : 16
% 1.84/1.14  #Fact    : 0
% 1.84/1.14  #Define  : 0
% 1.84/1.14  #Split   : 0
% 1.84/1.14  #Chain   : 0
% 1.84/1.14  #Close   : 0
% 1.84/1.14  
% 1.84/1.14  Ordering : KBO
% 1.84/1.14  
% 1.84/1.14  Simplification rules
% 1.84/1.14  ----------------------
% 1.84/1.14  #Subsume      : 0
% 1.84/1.14  #Demod        : 8
% 1.84/1.14  #Tautology    : 4
% 1.84/1.14  #SimpNegUnit  : 1
% 1.84/1.14  #BackRed      : 0
% 1.84/1.14  
% 1.84/1.14  #Partial instantiations: 0
% 1.84/1.14  #Strategies tried      : 1
% 1.84/1.14  
% 1.84/1.14  Timing (in seconds)
% 1.84/1.14  ----------------------
% 1.84/1.14  Preprocessing        : 0.28
% 1.84/1.14  Parsing              : 0.15
% 1.84/1.14  CNF conversion       : 0.02
% 1.84/1.14  Main loop            : 0.12
% 1.84/1.14  Inferencing          : 0.05
% 1.84/1.14  Reduction            : 0.03
% 1.84/1.14  Demodulation         : 0.03
% 1.84/1.14  BG Simplification    : 0.01
% 1.84/1.14  Subsumption          : 0.02
% 1.84/1.14  Abstraction          : 0.01
% 1.84/1.14  MUC search           : 0.00
% 1.84/1.14  Cooper               : 0.00
% 1.84/1.14  Total                : 0.42
% 1.84/1.14  Index Insertion      : 0.00
% 1.84/1.14  Index Deletion       : 0.00
% 1.84/1.14  Index Matching       : 0.00
% 1.84/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
