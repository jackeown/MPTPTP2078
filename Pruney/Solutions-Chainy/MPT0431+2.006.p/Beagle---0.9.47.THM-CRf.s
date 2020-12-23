%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:13 EST 2020

% Result     : Theorem 7.33s
% Output     : CNFRefutation 7.45s
% Verified   : 
% Statistics : Number of formulae       :   65 (  88 expanded)
%              Number of leaves         :   30 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 180 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v3_setfam_1(B,A)
              & m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A))) )
           => ! [C] :
                ( ( v3_setfam_1(C,A)
                  & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A))) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(A),B,C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_setfam_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_77,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_62,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_50,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(A,B)
        & r2_hidden(C,k2_xboole_0(A,B))
        & ~ ( r2_hidden(C,A)
            & ~ r2_hidden(C,B) )
        & ~ ( r2_hidden(C,B)
            & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_42,plain,(
    v3_setfam_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_94,plain,(
    ! [A_53,B_54] :
      ( ~ r2_hidden(A_53,B_54)
      | ~ v3_setfam_1(B_54,A_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k1_zfmisc_1(A_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_101,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | ~ v3_setfam_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_94])).

tff(c_108,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_101])).

tff(c_38,plain,(
    v3_setfam_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_104,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | ~ v3_setfam_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_94])).

tff(c_111,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_104])).

tff(c_168,plain,(
    ! [A_76,B_77,C_78] :
      ( k4_subset_1(A_76,B_77,C_78) = k2_xboole_0(B_77,C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(A_76))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_262,plain,(
    ! [B_80] :
      ( k4_subset_1(k1_zfmisc_1('#skF_1'),B_80,'#skF_3') = k2_xboole_0(B_80,'#skF_3')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_36,c_168])).

tff(c_287,plain,(
    k4_subset_1(k1_zfmisc_1('#skF_1'),'#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_262])).

tff(c_34,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_289,plain,(
    ~ v3_setfam_1(k2_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_34])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k4_subset_1(A_14,B_15,C_16),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_293,plain,
    ( m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_20])).

tff(c_297,plain,(
    m1_subset_1(k2_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_293])).

tff(c_30,plain,(
    ! [B_29,A_28] :
      ( v3_setfam_1(B_29,A_28)
      | r2_hidden(A_28,B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k1_zfmisc_1(A_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_309,plain,
    ( v3_setfam_1(k2_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | r2_hidden('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_297,c_30])).

tff(c_318,plain,(
    r2_hidden('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_309])).

tff(c_28,plain,(
    ! [A_26,B_27] : k6_subset_1(A_26,B_27) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [A_17,B_18] : m1_subset_1(k6_subset_1(A_17,B_18),k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_45,plain,(
    ! [A_17,B_18] : m1_subset_1(k4_xboole_0(A_17,B_18),k1_zfmisc_1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_xboole_0(k4_xboole_0(A_8,B_9),B_9) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_48,plain,(
    ! [B_38,A_39] :
      ( r1_xboole_0(B_38,A_39)
      | ~ r1_xboole_0(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    ! [B_9,A_8] : r1_xboole_0(B_9,k4_xboole_0(A_8,B_9)) ),
    inference(resolution,[status(thm)],[c_14,c_48])).

tff(c_12,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_130,plain,(
    ! [C_57,A_58,B_59] :
      ( r2_hidden(C_57,A_58)
      | r2_hidden(C_57,B_59)
      | ~ r2_hidden(C_57,k2_xboole_0(A_58,B_59))
      | ~ r1_xboole_0(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_133,plain,(
    ! [C_57,A_6,B_7] :
      ( r2_hidden(C_57,A_6)
      | r2_hidden(C_57,k4_xboole_0(B_7,A_6))
      | ~ r2_hidden(C_57,k2_xboole_0(A_6,B_7))
      | ~ r1_xboole_0(A_6,k4_xboole_0(B_7,A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_130])).

tff(c_142,plain,(
    ! [C_64,A_65,B_66] :
      ( r2_hidden(C_64,A_65)
      | r2_hidden(C_64,k4_xboole_0(B_66,A_65))
      | ~ r2_hidden(C_64,k2_xboole_0(A_65,B_66)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_133])).

tff(c_24,plain,(
    ! [C_22,A_19,B_20] :
      ( r2_hidden(C_22,A_19)
      | ~ r2_hidden(C_22,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6621,plain,(
    ! [C_236,A_237,B_238,A_239] :
      ( r2_hidden(C_236,A_237)
      | ~ m1_subset_1(k4_xboole_0(B_238,A_239),k1_zfmisc_1(A_237))
      | r2_hidden(C_236,A_239)
      | ~ r2_hidden(C_236,k2_xboole_0(A_239,B_238)) ) ),
    inference(resolution,[status(thm)],[c_142,c_24])).

tff(c_6625,plain,(
    ! [C_240,A_241,B_242] :
      ( r2_hidden(C_240,A_241)
      | r2_hidden(C_240,B_242)
      | ~ r2_hidden(C_240,k2_xboole_0(B_242,A_241)) ) ),
    inference(resolution,[status(thm)],[c_45,c_6621])).

tff(c_6634,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_318,c_6625])).

tff(c_6650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_111,c_6634])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.33/2.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.33/2.59  
% 7.33/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.33/2.59  %$ v3_setfam_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 7.33/2.59  
% 7.33/2.59  %Foreground sorts:
% 7.33/2.59  
% 7.33/2.59  
% 7.33/2.59  %Background operators:
% 7.33/2.59  
% 7.33/2.59  
% 7.33/2.59  %Foreground operators:
% 7.33/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.33/2.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.33/2.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.33/2.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.33/2.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.33/2.59  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.33/2.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.33/2.59  tff('#skF_2', type, '#skF_2': $i).
% 7.33/2.59  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 7.33/2.59  tff('#skF_3', type, '#skF_3': $i).
% 7.33/2.59  tff('#skF_1', type, '#skF_1': $i).
% 7.33/2.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.33/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.33/2.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.33/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.33/2.59  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 7.33/2.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.33/2.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.33/2.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.33/2.59  
% 7.45/2.60  tff(f_100, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((v3_setfam_1(B, A) & m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A)))) => (![C]: ((v3_setfam_1(C, A) & m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A)))) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(A), B, C), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_setfam_1)).
% 7.45/2.60  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_setfam_1)).
% 7.45/2.60  tff(f_75, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 7.45/2.60  tff(f_60, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 7.45/2.60  tff(f_77, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 7.45/2.60  tff(f_62, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 7.45/2.60  tff(f_50, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 7.45/2.60  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.45/2.60  tff(f_48, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.45/2.60  tff(f_46, axiom, (![A, B, C]: ~(((r1_xboole_0(A, B) & r2_hidden(C, k2_xboole_0(A, B))) & ~(r2_hidden(C, A) & ~r2_hidden(C, B))) & ~(r2_hidden(C, B) & ~r2_hidden(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_0)).
% 7.45/2.60  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 7.45/2.60  tff(c_42, plain, (v3_setfam_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.45/2.60  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.45/2.60  tff(c_94, plain, (![A_53, B_54]: (~r2_hidden(A_53, B_54) | ~v3_setfam_1(B_54, A_53) | ~m1_subset_1(B_54, k1_zfmisc_1(k1_zfmisc_1(A_53))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.45/2.60  tff(c_101, plain, (~r2_hidden('#skF_1', '#skF_2') | ~v3_setfam_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_94])).
% 7.45/2.60  tff(c_108, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_101])).
% 7.45/2.60  tff(c_38, plain, (v3_setfam_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.45/2.60  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.45/2.60  tff(c_104, plain, (~r2_hidden('#skF_1', '#skF_3') | ~v3_setfam_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_94])).
% 7.45/2.60  tff(c_111, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_104])).
% 7.45/2.60  tff(c_168, plain, (![A_76, B_77, C_78]: (k4_subset_1(A_76, B_77, C_78)=k2_xboole_0(B_77, C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(A_76)) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.45/2.60  tff(c_262, plain, (![B_80]: (k4_subset_1(k1_zfmisc_1('#skF_1'), B_80, '#skF_3')=k2_xboole_0(B_80, '#skF_3') | ~m1_subset_1(B_80, k1_zfmisc_1(k1_zfmisc_1('#skF_1'))))), inference(resolution, [status(thm)], [c_36, c_168])).
% 7.45/2.60  tff(c_287, plain, (k4_subset_1(k1_zfmisc_1('#skF_1'), '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_262])).
% 7.45/2.60  tff(c_34, plain, (~v3_setfam_1(k4_subset_1(k1_zfmisc_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.45/2.60  tff(c_289, plain, (~v3_setfam_1(k2_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_34])).
% 7.45/2.60  tff(c_20, plain, (![A_14, B_15, C_16]: (m1_subset_1(k4_subset_1(A_14, B_15, C_16), k1_zfmisc_1(A_14)) | ~m1_subset_1(C_16, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.45/2.60  tff(c_293, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_287, c_20])).
% 7.45/2.60  tff(c_297, plain, (m1_subset_1(k2_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_293])).
% 7.45/2.60  tff(c_30, plain, (![B_29, A_28]: (v3_setfam_1(B_29, A_28) | r2_hidden(A_28, B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(k1_zfmisc_1(A_28))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.45/2.60  tff(c_309, plain, (v3_setfam_1(k2_xboole_0('#skF_2', '#skF_3'), '#skF_1') | r2_hidden('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_297, c_30])).
% 7.45/2.60  tff(c_318, plain, (r2_hidden('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_289, c_309])).
% 7.45/2.60  tff(c_28, plain, (![A_26, B_27]: (k6_subset_1(A_26, B_27)=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.45/2.60  tff(c_22, plain, (![A_17, B_18]: (m1_subset_1(k6_subset_1(A_17, B_18), k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.45/2.60  tff(c_45, plain, (![A_17, B_18]: (m1_subset_1(k4_xboole_0(A_17, B_18), k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22])).
% 7.45/2.60  tff(c_14, plain, (![A_8, B_9]: (r1_xboole_0(k4_xboole_0(A_8, B_9), B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.45/2.60  tff(c_48, plain, (![B_38, A_39]: (r1_xboole_0(B_38, A_39) | ~r1_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.45/2.60  tff(c_51, plain, (![B_9, A_8]: (r1_xboole_0(B_9, k4_xboole_0(A_8, B_9)))), inference(resolution, [status(thm)], [c_14, c_48])).
% 7.45/2.60  tff(c_12, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.45/2.60  tff(c_130, plain, (![C_57, A_58, B_59]: (r2_hidden(C_57, A_58) | r2_hidden(C_57, B_59) | ~r2_hidden(C_57, k2_xboole_0(A_58, B_59)) | ~r1_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.45/2.60  tff(c_133, plain, (![C_57, A_6, B_7]: (r2_hidden(C_57, A_6) | r2_hidden(C_57, k4_xboole_0(B_7, A_6)) | ~r2_hidden(C_57, k2_xboole_0(A_6, B_7)) | ~r1_xboole_0(A_6, k4_xboole_0(B_7, A_6)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_130])).
% 7.45/2.60  tff(c_142, plain, (![C_64, A_65, B_66]: (r2_hidden(C_64, A_65) | r2_hidden(C_64, k4_xboole_0(B_66, A_65)) | ~r2_hidden(C_64, k2_xboole_0(A_65, B_66)))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_133])).
% 7.45/2.60  tff(c_24, plain, (![C_22, A_19, B_20]: (r2_hidden(C_22, A_19) | ~r2_hidden(C_22, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.45/2.60  tff(c_6621, plain, (![C_236, A_237, B_238, A_239]: (r2_hidden(C_236, A_237) | ~m1_subset_1(k4_xboole_0(B_238, A_239), k1_zfmisc_1(A_237)) | r2_hidden(C_236, A_239) | ~r2_hidden(C_236, k2_xboole_0(A_239, B_238)))), inference(resolution, [status(thm)], [c_142, c_24])).
% 7.45/2.60  tff(c_6625, plain, (![C_240, A_241, B_242]: (r2_hidden(C_240, A_241) | r2_hidden(C_240, B_242) | ~r2_hidden(C_240, k2_xboole_0(B_242, A_241)))), inference(resolution, [status(thm)], [c_45, c_6621])).
% 7.45/2.60  tff(c_6634, plain, (r2_hidden('#skF_1', '#skF_3') | r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_318, c_6625])).
% 7.45/2.60  tff(c_6650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_111, c_6634])).
% 7.45/2.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.45/2.60  
% 7.45/2.60  Inference rules
% 7.45/2.60  ----------------------
% 7.45/2.60  #Ref     : 0
% 7.45/2.60  #Sup     : 1606
% 7.45/2.60  #Fact    : 0
% 7.45/2.60  #Define  : 0
% 7.45/2.60  #Split   : 16
% 7.45/2.60  #Chain   : 0
% 7.45/2.60  #Close   : 0
% 7.45/2.60  
% 7.45/2.60  Ordering : KBO
% 7.45/2.60  
% 7.45/2.60  Simplification rules
% 7.45/2.60  ----------------------
% 7.45/2.60  #Subsume      : 30
% 7.45/2.60  #Demod        : 1534
% 7.45/2.60  #Tautology    : 248
% 7.45/2.60  #SimpNegUnit  : 35
% 7.45/2.61  #BackRed      : 1
% 7.45/2.61  
% 7.45/2.61  #Partial instantiations: 0
% 7.45/2.61  #Strategies tried      : 1
% 7.45/2.61  
% 7.45/2.61  Timing (in seconds)
% 7.45/2.61  ----------------------
% 7.45/2.61  Preprocessing        : 0.31
% 7.45/2.61  Parsing              : 0.17
% 7.45/2.61  CNF conversion       : 0.02
% 7.45/2.61  Main loop            : 1.52
% 7.45/2.61  Inferencing          : 0.46
% 7.45/2.61  Reduction            : 0.60
% 7.45/2.61  Demodulation         : 0.46
% 7.45/2.61  BG Simplification    : 0.06
% 7.45/2.61  Subsumption          : 0.29
% 7.45/2.61  Abstraction          : 0.09
% 7.45/2.61  MUC search           : 0.00
% 7.45/2.61  Cooper               : 0.00
% 7.45/2.61  Total                : 1.87
% 7.45/2.61  Index Insertion      : 0.00
% 7.45/2.61  Index Deletion       : 0.00
% 7.45/2.61  Index Matching       : 0.00
% 7.45/2.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
