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
% DateTime   : Thu Dec  3 09:55:39 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   66 (  93 expanded)
%              Number of leaves         :   33 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 142 expanded)
%              Number of equality atoms :   27 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_51,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    ! [A_38] : k2_subset_1(A_38) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    ! [A_39] : m1_subset_1(k2_subset_1(A_39),k1_zfmisc_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_41,plain,(
    ! [A_39] : m1_subset_1(A_39,k1_zfmisc_1(A_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_272,plain,(
    ! [A_89,B_90,C_91] :
      ( k4_subset_1(A_89,B_90,C_91) = k2_xboole_0(B_90,C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(A_89))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_296,plain,(
    ! [A_93,B_94] :
      ( k4_subset_1(A_93,B_94,A_93) = k2_xboole_0(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(resolution,[status(thm)],[c_41,c_272])).

tff(c_301,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_296])).

tff(c_38,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_38])).

tff(c_312,plain,(
    k2_xboole_0('#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_42])).

tff(c_349,plain,(
    ! [A_112,B_113,C_114] :
      ( r2_hidden('#skF_1'(A_112,B_113,C_114),B_113)
      | r1_tarski(B_113,C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(A_112))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [C_43,A_40,B_41] :
      ( r2_hidden(C_43,A_40)
      | ~ r2_hidden(C_43,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_374,plain,(
    ! [A_120,B_121,C_122,A_123] :
      ( r2_hidden('#skF_1'(A_120,B_121,C_122),A_123)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_123))
      | r1_tarski(B_121,C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(A_120))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_120)) ) ),
    inference(resolution,[status(thm)],[c_349,c_28])).

tff(c_32,plain,(
    ! [A_47,B_48,C_52] :
      ( ~ r2_hidden('#skF_1'(A_47,B_48,C_52),C_52)
      | r1_tarski(B_48,C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_47))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_456,plain,(
    ! [B_132,A_133,A_134] :
      ( ~ m1_subset_1(B_132,k1_zfmisc_1(A_133))
      | r1_tarski(B_132,A_133)
      | ~ m1_subset_1(A_133,k1_zfmisc_1(A_134))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_134)) ) ),
    inference(resolution,[status(thm)],[c_374,c_32])).

tff(c_465,plain,(
    ! [A_134] :
      ( r1_tarski('#skF_3','#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(A_134))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_134)) ) ),
    inference(resolution,[status(thm)],[c_40,c_456])).

tff(c_469,plain,(
    ! [A_135] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(A_135))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_135)) ) ),
    inference(splitLeft,[status(thm)],[c_465])).

tff(c_473,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_41,c_469])).

tff(c_477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_473])).

tff(c_478,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_465])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_482,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_478,c_6])).

tff(c_95,plain,(
    ! [B_60,A_61] : k3_xboole_0(B_60,A_61) = k3_xboole_0(A_61,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_110,plain,(
    ! [A_61,B_60] : k2_xboole_0(A_61,k3_xboole_0(B_60,A_61)) = A_61 ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_4])).

tff(c_486,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_110])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_162,plain,(
    ! [A_64,B_65] : k3_tarski(k2_tarski(A_64,B_65)) = k2_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_187,plain,(
    ! [B_70,A_71] : k3_tarski(k2_tarski(B_70,A_71)) = k2_xboole_0(A_71,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_162])).

tff(c_22,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_193,plain,(
    ! [B_70,A_71] : k2_xboole_0(B_70,A_71) = k2_xboole_0(A_71,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_22])).

tff(c_497,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_193])).

tff(c_510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_497])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n025.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 11:41:50 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.31  
% 2.19/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.19/1.32  
% 2.19/1.32  %Foreground sorts:
% 2.19/1.32  
% 2.19/1.32  
% 2.19/1.32  %Background operators:
% 2.19/1.32  
% 2.19/1.32  
% 2.19/1.32  %Foreground operators:
% 2.19/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.19/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.32  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.19/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.19/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.19/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.32  
% 2.65/1.33  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 2.65/1.33  tff(f_51, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.65/1.33  tff(f_53, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.65/1.33  tff(f_66, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.65/1.33  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 2.65/1.33  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.65/1.33  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.65/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.65/1.33  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.65/1.33  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.65/1.33  tff(f_49, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.65/1.33  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.65/1.33  tff(c_24, plain, (![A_38]: (k2_subset_1(A_38)=A_38)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.65/1.33  tff(c_26, plain, (![A_39]: (m1_subset_1(k2_subset_1(A_39), k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.65/1.33  tff(c_41, plain, (![A_39]: (m1_subset_1(A_39, k1_zfmisc_1(A_39)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 2.65/1.33  tff(c_272, plain, (![A_89, B_90, C_91]: (k4_subset_1(A_89, B_90, C_91)=k2_xboole_0(B_90, C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(A_89)) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.65/1.33  tff(c_296, plain, (![A_93, B_94]: (k4_subset_1(A_93, B_94, A_93)=k2_xboole_0(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(resolution, [status(thm)], [c_41, c_272])).
% 2.65/1.33  tff(c_301, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_296])).
% 2.65/1.33  tff(c_38, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.65/1.33  tff(c_42, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_38])).
% 2.65/1.33  tff(c_312, plain, (k2_xboole_0('#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_301, c_42])).
% 2.65/1.33  tff(c_349, plain, (![A_112, B_113, C_114]: (r2_hidden('#skF_1'(A_112, B_113, C_114), B_113) | r1_tarski(B_113, C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(A_112)) | ~m1_subset_1(B_113, k1_zfmisc_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.65/1.33  tff(c_28, plain, (![C_43, A_40, B_41]: (r2_hidden(C_43, A_40) | ~r2_hidden(C_43, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.65/1.33  tff(c_374, plain, (![A_120, B_121, C_122, A_123]: (r2_hidden('#skF_1'(A_120, B_121, C_122), A_123) | ~m1_subset_1(B_121, k1_zfmisc_1(A_123)) | r1_tarski(B_121, C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(A_120)) | ~m1_subset_1(B_121, k1_zfmisc_1(A_120)))), inference(resolution, [status(thm)], [c_349, c_28])).
% 2.65/1.33  tff(c_32, plain, (![A_47, B_48, C_52]: (~r2_hidden('#skF_1'(A_47, B_48, C_52), C_52) | r1_tarski(B_48, C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(A_47)) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.65/1.33  tff(c_456, plain, (![B_132, A_133, A_134]: (~m1_subset_1(B_132, k1_zfmisc_1(A_133)) | r1_tarski(B_132, A_133) | ~m1_subset_1(A_133, k1_zfmisc_1(A_134)) | ~m1_subset_1(B_132, k1_zfmisc_1(A_134)))), inference(resolution, [status(thm)], [c_374, c_32])).
% 2.65/1.33  tff(c_465, plain, (![A_134]: (r1_tarski('#skF_3', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(A_134)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_134)))), inference(resolution, [status(thm)], [c_40, c_456])).
% 2.65/1.33  tff(c_469, plain, (![A_135]: (~m1_subset_1('#skF_2', k1_zfmisc_1(A_135)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_135)))), inference(splitLeft, [status(thm)], [c_465])).
% 2.65/1.33  tff(c_473, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_41, c_469])).
% 2.65/1.33  tff(c_477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_473])).
% 2.65/1.33  tff(c_478, plain, (r1_tarski('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_465])).
% 2.65/1.33  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.65/1.33  tff(c_482, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_478, c_6])).
% 2.65/1.33  tff(c_95, plain, (![B_60, A_61]: (k3_xboole_0(B_60, A_61)=k3_xboole_0(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.65/1.33  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.65/1.33  tff(c_110, plain, (![A_61, B_60]: (k2_xboole_0(A_61, k3_xboole_0(B_60, A_61))=A_61)), inference(superposition, [status(thm), theory('equality')], [c_95, c_4])).
% 2.65/1.33  tff(c_486, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_482, c_110])).
% 2.65/1.33  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.65/1.33  tff(c_162, plain, (![A_64, B_65]: (k3_tarski(k2_tarski(A_64, B_65))=k2_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.65/1.33  tff(c_187, plain, (![B_70, A_71]: (k3_tarski(k2_tarski(B_70, A_71))=k2_xboole_0(A_71, B_70))), inference(superposition, [status(thm), theory('equality')], [c_8, c_162])).
% 2.65/1.33  tff(c_22, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.65/1.33  tff(c_193, plain, (![B_70, A_71]: (k2_xboole_0(B_70, A_71)=k2_xboole_0(A_71, B_70))), inference(superposition, [status(thm), theory('equality')], [c_187, c_22])).
% 2.65/1.33  tff(c_497, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_486, c_193])).
% 2.65/1.33  tff(c_510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_312, c_497])).
% 2.65/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.33  
% 2.65/1.33  Inference rules
% 2.65/1.33  ----------------------
% 2.65/1.33  #Ref     : 0
% 2.65/1.33  #Sup     : 117
% 2.65/1.33  #Fact    : 0
% 2.65/1.33  #Define  : 0
% 2.65/1.33  #Split   : 1
% 2.65/1.33  #Chain   : 0
% 2.65/1.33  #Close   : 0
% 2.65/1.33  
% 2.65/1.33  Ordering : KBO
% 2.65/1.33  
% 2.65/1.33  Simplification rules
% 2.65/1.33  ----------------------
% 2.65/1.33  #Subsume      : 5
% 2.65/1.33  #Demod        : 24
% 2.65/1.33  #Tautology    : 81
% 2.65/1.33  #SimpNegUnit  : 1
% 2.65/1.33  #BackRed      : 3
% 2.65/1.33  
% 2.65/1.33  #Partial instantiations: 0
% 2.65/1.33  #Strategies tried      : 1
% 2.65/1.33  
% 2.65/1.33  Timing (in seconds)
% 2.65/1.33  ----------------------
% 2.65/1.33  Preprocessing        : 0.31
% 2.65/1.33  Parsing              : 0.17
% 2.65/1.34  CNF conversion       : 0.02
% 2.65/1.34  Main loop            : 0.28
% 2.65/1.34  Inferencing          : 0.10
% 2.65/1.34  Reduction            : 0.09
% 2.65/1.34  Demodulation         : 0.07
% 2.65/1.34  BG Simplification    : 0.02
% 2.65/1.34  Subsumption          : 0.05
% 2.65/1.34  Abstraction          : 0.02
% 2.65/1.34  MUC search           : 0.00
% 2.65/1.34  Cooper               : 0.00
% 2.65/1.34  Total                : 0.63
% 2.65/1.34  Index Insertion      : 0.00
% 2.65/1.34  Index Deletion       : 0.00
% 2.65/1.34  Index Matching       : 0.00
% 2.65/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
