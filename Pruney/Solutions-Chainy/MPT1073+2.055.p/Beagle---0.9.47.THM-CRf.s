%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:05 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   65 (  99 expanded)
%              Number of leaves         :   33 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 194 expanded)
%              Number of equality atoms :   19 (  38 expanded)
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

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_116,plain,(
    ! [A_63,B_64,C_65,D_66] :
      ( k7_relset_1(A_63,B_64,C_65,D_66) = k9_relat_1(C_65,D_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_123,plain,(
    ! [D_66] : k7_relset_1('#skF_3','#skF_4','#skF_5',D_66) = k9_relat_1('#skF_5',D_66) ),
    inference(resolution,[status(thm)],[c_36,c_116])).

tff(c_210,plain,(
    ! [A_81,B_82,C_83] :
      ( k7_relset_1(A_81,B_82,C_83,A_81) = k2_relset_1(A_81,B_82,C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_215,plain,(
    k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_3') = k2_relset_1('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_210])).

tff(c_218,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k9_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_215])).

tff(c_34,plain,(
    r2_hidden('#skF_2',k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_219,plain,(
    r2_hidden('#skF_2',k9_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_34])).

tff(c_6,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_43,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_43])).

tff(c_49,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_46])).

tff(c_133,plain,(
    ! [A_68,B_69,C_70] :
      ( r2_hidden('#skF_1'(A_68,B_69,C_70),k1_relat_1(C_70))
      | ~ r2_hidden(A_68,k9_relat_1(C_70,B_69))
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_55,plain,(
    ! [A_42,B_43,C_44] :
      ( k1_relset_1(A_42,B_43,C_44) = k1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_59,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_55])).

tff(c_64,plain,(
    ! [A_45,B_46,C_47] :
      ( m1_subset_1(k1_relset_1(A_45,B_46,C_47),k1_zfmisc_1(A_45))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_76,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_64])).

tff(c_81,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_76])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_3')
      | ~ r2_hidden(A_1,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_81,c_2])).

tff(c_137,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1('#skF_1'(A_68,B_69,'#skF_5'),'#skF_3')
      | ~ r2_hidden(A_68,k9_relat_1('#skF_5',B_69))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_133,c_87])).

tff(c_140,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1('#skF_1'(A_68,B_69,'#skF_5'),'#skF_3')
      | ~ r2_hidden(A_68,k9_relat_1('#skF_5',B_69)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_137])).

tff(c_227,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_219,c_140])).

tff(c_32,plain,(
    ! [E_32] :
      ( k1_funct_1('#skF_5',E_32) != '#skF_2'
      | ~ m1_subset_1(E_32,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_247,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_227,c_32])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_160,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden(k4_tarski('#skF_1'(A_76,B_77,C_78),A_76),C_78)
      | ~ r2_hidden(A_76,k9_relat_1(C_78,B_77))
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [C_17,A_15,B_16] :
      ( k1_funct_1(C_17,A_15) = B_16
      | ~ r2_hidden(k4_tarski(A_15,B_16),C_17)
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_286,plain,(
    ! [C_94,A_95,B_96] :
      ( k1_funct_1(C_94,'#skF_1'(A_95,B_96,C_94)) = A_95
      | ~ v1_funct_1(C_94)
      | ~ r2_hidden(A_95,k9_relat_1(C_94,B_96))
      | ~ v1_relat_1(C_94) ) ),
    inference(resolution,[status(thm)],[c_160,c_18])).

tff(c_290,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_219,c_286])).

tff(c_303,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2','#skF_3','#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_40,c_290])).

tff(c_305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:33:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.39  
% 2.40/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.40  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.40/1.40  
% 2.40/1.40  %Foreground sorts:
% 2.40/1.40  
% 2.40/1.40  
% 2.40/1.40  %Background operators:
% 2.40/1.40  
% 2.40/1.40  
% 2.40/1.40  %Foreground operators:
% 2.40/1.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.40/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.40/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.40/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.40/1.40  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.40/1.40  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.40/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.40/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.40/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.40/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.40/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.40/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.40/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.40/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.40/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.40/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.40  
% 2.40/1.41  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 2.40/1.41  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.40/1.41  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.40/1.41  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.40/1.41  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.40/1.41  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.40/1.41  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.40/1.41  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.40/1.41  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.40/1.41  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.40/1.41  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.40/1.41  tff(c_116, plain, (![A_63, B_64, C_65, D_66]: (k7_relset_1(A_63, B_64, C_65, D_66)=k9_relat_1(C_65, D_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.40/1.41  tff(c_123, plain, (![D_66]: (k7_relset_1('#skF_3', '#skF_4', '#skF_5', D_66)=k9_relat_1('#skF_5', D_66))), inference(resolution, [status(thm)], [c_36, c_116])).
% 2.40/1.41  tff(c_210, plain, (![A_81, B_82, C_83]: (k7_relset_1(A_81, B_82, C_83, A_81)=k2_relset_1(A_81, B_82, C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.40/1.41  tff(c_215, plain, (k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_3')=k2_relset_1('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_210])).
% 2.40/1.41  tff(c_218, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k9_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_215])).
% 2.40/1.41  tff(c_34, plain, (r2_hidden('#skF_2', k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.40/1.41  tff(c_219, plain, (r2_hidden('#skF_2', k9_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_34])).
% 2.40/1.41  tff(c_6, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.40/1.41  tff(c_43, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.40/1.41  tff(c_46, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_43])).
% 2.40/1.41  tff(c_49, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_46])).
% 2.40/1.41  tff(c_133, plain, (![A_68, B_69, C_70]: (r2_hidden('#skF_1'(A_68, B_69, C_70), k1_relat_1(C_70)) | ~r2_hidden(A_68, k9_relat_1(C_70, B_69)) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.40/1.41  tff(c_55, plain, (![A_42, B_43, C_44]: (k1_relset_1(A_42, B_43, C_44)=k1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.40/1.41  tff(c_59, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_55])).
% 2.40/1.41  tff(c_64, plain, (![A_45, B_46, C_47]: (m1_subset_1(k1_relset_1(A_45, B_46, C_47), k1_zfmisc_1(A_45)) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.40/1.41  tff(c_76, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_59, c_64])).
% 2.40/1.41  tff(c_81, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_76])).
% 2.40/1.41  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.40/1.41  tff(c_87, plain, (![A_1]: (m1_subset_1(A_1, '#skF_3') | ~r2_hidden(A_1, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_81, c_2])).
% 2.40/1.41  tff(c_137, plain, (![A_68, B_69]: (m1_subset_1('#skF_1'(A_68, B_69, '#skF_5'), '#skF_3') | ~r2_hidden(A_68, k9_relat_1('#skF_5', B_69)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_133, c_87])).
% 2.40/1.41  tff(c_140, plain, (![A_68, B_69]: (m1_subset_1('#skF_1'(A_68, B_69, '#skF_5'), '#skF_3') | ~r2_hidden(A_68, k9_relat_1('#skF_5', B_69)))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_137])).
% 2.40/1.41  tff(c_227, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_219, c_140])).
% 2.40/1.41  tff(c_32, plain, (![E_32]: (k1_funct_1('#skF_5', E_32)!='#skF_2' | ~m1_subset_1(E_32, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.40/1.41  tff(c_247, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))!='#skF_2'), inference(resolution, [status(thm)], [c_227, c_32])).
% 2.40/1.41  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.40/1.41  tff(c_160, plain, (![A_76, B_77, C_78]: (r2_hidden(k4_tarski('#skF_1'(A_76, B_77, C_78), A_76), C_78) | ~r2_hidden(A_76, k9_relat_1(C_78, B_77)) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.40/1.41  tff(c_18, plain, (![C_17, A_15, B_16]: (k1_funct_1(C_17, A_15)=B_16 | ~r2_hidden(k4_tarski(A_15, B_16), C_17) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.40/1.41  tff(c_286, plain, (![C_94, A_95, B_96]: (k1_funct_1(C_94, '#skF_1'(A_95, B_96, C_94))=A_95 | ~v1_funct_1(C_94) | ~r2_hidden(A_95, k9_relat_1(C_94, B_96)) | ~v1_relat_1(C_94))), inference(resolution, [status(thm)], [c_160, c_18])).
% 2.40/1.41  tff(c_290, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_219, c_286])).
% 2.40/1.41  tff(c_303, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_2', '#skF_3', '#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_49, c_40, c_290])).
% 2.40/1.41  tff(c_305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_247, c_303])).
% 2.40/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.41  
% 2.40/1.41  Inference rules
% 2.40/1.41  ----------------------
% 2.40/1.41  #Ref     : 0
% 2.40/1.41  #Sup     : 59
% 2.40/1.41  #Fact    : 0
% 2.40/1.41  #Define  : 0
% 2.40/1.41  #Split   : 2
% 2.40/1.41  #Chain   : 0
% 2.40/1.41  #Close   : 0
% 2.40/1.41  
% 2.40/1.41  Ordering : KBO
% 2.40/1.41  
% 2.40/1.41  Simplification rules
% 2.40/1.41  ----------------------
% 2.40/1.41  #Subsume      : 4
% 2.40/1.41  #Demod        : 11
% 2.40/1.41  #Tautology    : 10
% 2.40/1.41  #SimpNegUnit  : 1
% 2.40/1.41  #BackRed      : 1
% 2.40/1.41  
% 2.40/1.41  #Partial instantiations: 0
% 2.40/1.41  #Strategies tried      : 1
% 2.40/1.41  
% 2.40/1.41  Timing (in seconds)
% 2.40/1.41  ----------------------
% 2.40/1.41  Preprocessing        : 0.32
% 2.40/1.41  Parsing              : 0.17
% 2.40/1.41  CNF conversion       : 0.02
% 2.40/1.41  Main loop            : 0.23
% 2.40/1.41  Inferencing          : 0.08
% 2.40/1.41  Reduction            : 0.07
% 2.40/1.41  Demodulation         : 0.05
% 2.40/1.41  BG Simplification    : 0.02
% 2.40/1.41  Subsumption          : 0.04
% 2.40/1.41  Abstraction          : 0.02
% 2.40/1.41  MUC search           : 0.00
% 2.40/1.41  Cooper               : 0.00
% 2.40/1.41  Total                : 0.58
% 2.40/1.41  Index Insertion      : 0.00
% 2.40/1.41  Index Deletion       : 0.00
% 2.40/1.41  Index Matching       : 0.00
% 2.40/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
