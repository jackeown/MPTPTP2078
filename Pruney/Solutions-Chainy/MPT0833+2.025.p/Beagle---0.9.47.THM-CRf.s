%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:48 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   64 (  81 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 132 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k2_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_70,plain,(
    ! [A_49,B_50,D_51] :
      ( r2_relset_1(A_49,B_50,D_51,D_51)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_73,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_70])).

tff(c_12,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_32,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_35,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_32])).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_35])).

tff(c_74,plain,(
    ! [A_52,B_53,C_54] :
      ( k2_relset_1(A_52,B_53,C_54) = k2_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_78,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_74])).

tff(c_107,plain,(
    ! [A_61,B_62,C_63] :
      ( m1_subset_1(k2_relset_1(A_61,B_62,C_63),k1_zfmisc_1(B_62))
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_120,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_107])).

tff(c_125,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_120])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,(
    ! [C_46,A_47,B_48] :
      ( r2_hidden(C_46,A_47)
      | ~ r2_hidden(C_46,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_95,plain,(
    ! [A_58,B_59,A_60] :
      ( r2_hidden('#skF_1'(A_58,B_59),A_60)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(A_60))
      | r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_66])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_131,plain,(
    ! [A_64,A_65] :
      ( ~ m1_subset_1(A_64,k1_zfmisc_1(A_65))
      | r1_tarski(A_64,A_65) ) ),
    inference(resolution,[status(thm)],[c_95,c_4])).

tff(c_141,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_125,c_131])).

tff(c_28,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_47,plain,(
    ! [C_40,B_41,A_42] :
      ( r2_hidden(C_40,B_41)
      | ~ r2_hidden(C_40,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,(
    ! [A_55,B_56,B_57] :
      ( r2_hidden('#skF_1'(A_55,B_56),B_57)
      | ~ r1_tarski(A_55,B_57)
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_192,plain,(
    ! [A_77,B_78,B_79,B_80] :
      ( r2_hidden('#skF_1'(A_77,B_78),B_79)
      | ~ r1_tarski(B_80,B_79)
      | ~ r1_tarski(A_77,B_80)
      | r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_83,c_2])).

tff(c_205,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_1'(A_81,B_82),'#skF_4')
      | ~ r1_tarski(A_81,'#skF_3')
      | r1_tarski(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_28,c_192])).

tff(c_217,plain,(
    ! [A_83] :
      ( ~ r1_tarski(A_83,'#skF_3')
      | r1_tarski(A_83,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_205,c_4])).

tff(c_225,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_217])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( k8_relat_1(A_15,B_16) = B_16
      | ~ r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_239,plain,
    ( k8_relat_1('#skF_4','#skF_5') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_225,c_14])).

tff(c_243,plain,(
    k8_relat_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_239])).

tff(c_150,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( k6_relset_1(A_66,B_67,C_68,D_69) = k8_relat_1(C_68,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_157,plain,(
    ! [C_68] : k6_relset_1('#skF_2','#skF_3',C_68,'#skF_5') = k8_relat_1(C_68,'#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_150])).

tff(c_26,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k6_relset_1('#skF_2','#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_162,plain,(
    ~ r2_relset_1('#skF_2','#skF_3',k8_relat_1('#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_26])).

tff(c_244,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_162])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_244])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:47:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.30  
% 2.09/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.30  %$ r2_relset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k2_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.09/1.30  
% 2.09/1.30  %Foreground sorts:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Background operators:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Foreground operators:
% 2.09/1.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.09/1.30  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.30  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.09/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.30  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.09/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.09/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.30  
% 2.29/1.31  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_relset_1)).
% 2.29/1.31  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.29/1.31  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.29/1.31  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.29/1.31  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.29/1.31  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.29/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.29/1.31  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.29/1.31  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.29/1.31  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.29/1.31  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.29/1.31  tff(c_70, plain, (![A_49, B_50, D_51]: (r2_relset_1(A_49, B_50, D_51, D_51) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.29/1.31  tff(c_73, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_70])).
% 2.29/1.31  tff(c_12, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.29/1.31  tff(c_32, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.29/1.31  tff(c_35, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_32])).
% 2.29/1.31  tff(c_38, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_35])).
% 2.29/1.31  tff(c_74, plain, (![A_52, B_53, C_54]: (k2_relset_1(A_52, B_53, C_54)=k2_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.29/1.31  tff(c_78, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_74])).
% 2.29/1.31  tff(c_107, plain, (![A_61, B_62, C_63]: (m1_subset_1(k2_relset_1(A_61, B_62, C_63), k1_zfmisc_1(B_62)) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.29/1.31  tff(c_120, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_78, c_107])).
% 2.29/1.31  tff(c_125, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_120])).
% 2.29/1.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.31  tff(c_66, plain, (![C_46, A_47, B_48]: (r2_hidden(C_46, A_47) | ~r2_hidden(C_46, B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.29/1.31  tff(c_95, plain, (![A_58, B_59, A_60]: (r2_hidden('#skF_1'(A_58, B_59), A_60) | ~m1_subset_1(A_58, k1_zfmisc_1(A_60)) | r1_tarski(A_58, B_59))), inference(resolution, [status(thm)], [c_6, c_66])).
% 2.29/1.31  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.31  tff(c_131, plain, (![A_64, A_65]: (~m1_subset_1(A_64, k1_zfmisc_1(A_65)) | r1_tarski(A_64, A_65))), inference(resolution, [status(thm)], [c_95, c_4])).
% 2.29/1.31  tff(c_141, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_125, c_131])).
% 2.29/1.31  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.29/1.31  tff(c_47, plain, (![C_40, B_41, A_42]: (r2_hidden(C_40, B_41) | ~r2_hidden(C_40, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.31  tff(c_83, plain, (![A_55, B_56, B_57]: (r2_hidden('#skF_1'(A_55, B_56), B_57) | ~r1_tarski(A_55, B_57) | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_6, c_47])).
% 2.29/1.31  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.31  tff(c_192, plain, (![A_77, B_78, B_79, B_80]: (r2_hidden('#skF_1'(A_77, B_78), B_79) | ~r1_tarski(B_80, B_79) | ~r1_tarski(A_77, B_80) | r1_tarski(A_77, B_78))), inference(resolution, [status(thm)], [c_83, c_2])).
% 2.29/1.31  tff(c_205, plain, (![A_81, B_82]: (r2_hidden('#skF_1'(A_81, B_82), '#skF_4') | ~r1_tarski(A_81, '#skF_3') | r1_tarski(A_81, B_82))), inference(resolution, [status(thm)], [c_28, c_192])).
% 2.29/1.31  tff(c_217, plain, (![A_83]: (~r1_tarski(A_83, '#skF_3') | r1_tarski(A_83, '#skF_4'))), inference(resolution, [status(thm)], [c_205, c_4])).
% 2.29/1.31  tff(c_225, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_141, c_217])).
% 2.29/1.31  tff(c_14, plain, (![A_15, B_16]: (k8_relat_1(A_15, B_16)=B_16 | ~r1_tarski(k2_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.29/1.31  tff(c_239, plain, (k8_relat_1('#skF_4', '#skF_5')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_225, c_14])).
% 2.29/1.31  tff(c_243, plain, (k8_relat_1('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_239])).
% 2.29/1.31  tff(c_150, plain, (![A_66, B_67, C_68, D_69]: (k6_relset_1(A_66, B_67, C_68, D_69)=k8_relat_1(C_68, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.29/1.31  tff(c_157, plain, (![C_68]: (k6_relset_1('#skF_2', '#skF_3', C_68, '#skF_5')=k8_relat_1(C_68, '#skF_5'))), inference(resolution, [status(thm)], [c_30, c_150])).
% 2.29/1.31  tff(c_26, plain, (~r2_relset_1('#skF_2', '#skF_3', k6_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.29/1.31  tff(c_162, plain, (~r2_relset_1('#skF_2', '#skF_3', k8_relat_1('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_26])).
% 2.29/1.31  tff(c_244, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_162])).
% 2.29/1.31  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_244])).
% 2.29/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.31  
% 2.29/1.31  Inference rules
% 2.29/1.31  ----------------------
% 2.29/1.31  #Ref     : 0
% 2.29/1.31  #Sup     : 48
% 2.29/1.31  #Fact    : 0
% 2.29/1.31  #Define  : 0
% 2.29/1.31  #Split   : 1
% 2.29/1.31  #Chain   : 0
% 2.29/1.31  #Close   : 0
% 2.29/1.31  
% 2.29/1.31  Ordering : KBO
% 2.29/1.31  
% 2.29/1.31  Simplification rules
% 2.29/1.31  ----------------------
% 2.29/1.31  #Subsume      : 2
% 2.29/1.31  #Demod        : 12
% 2.29/1.31  #Tautology    : 12
% 2.29/1.31  #SimpNegUnit  : 0
% 2.29/1.31  #BackRed      : 2
% 2.29/1.31  
% 2.29/1.31  #Partial instantiations: 0
% 2.29/1.31  #Strategies tried      : 1
% 2.29/1.31  
% 2.29/1.31  Timing (in seconds)
% 2.29/1.31  ----------------------
% 2.29/1.32  Preprocessing        : 0.30
% 2.29/1.32  Parsing              : 0.16
% 2.29/1.32  CNF conversion       : 0.02
% 2.29/1.32  Main loop            : 0.20
% 2.29/1.32  Inferencing          : 0.08
% 2.29/1.32  Reduction            : 0.05
% 2.29/1.32  Demodulation         : 0.04
% 2.29/1.32  BG Simplification    : 0.01
% 2.29/1.32  Subsumption          : 0.04
% 2.29/1.32  Abstraction          : 0.01
% 2.29/1.32  MUC search           : 0.00
% 2.29/1.32  Cooper               : 0.00
% 2.29/1.32  Total                : 0.53
% 2.29/1.32  Index Insertion      : 0.00
% 2.29/1.32  Index Deletion       : 0.00
% 2.29/1.32  Index Matching       : 0.00
% 2.29/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
