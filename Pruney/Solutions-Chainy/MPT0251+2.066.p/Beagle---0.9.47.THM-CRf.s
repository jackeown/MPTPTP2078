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
% DateTime   : Thu Dec  3 09:50:55 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   65 (  71 expanded)
%              Number of leaves         :   33 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :   70 (  78 expanded)
%              Number of equality atoms :   31 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_66,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_48,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_282,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_2'(A_65,B_66),A_65)
      | r1_xboole_0(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_286,plain,(
    ! [A_65,B_66] :
      ( ~ v1_xboole_0(A_65)
      | r1_xboole_0(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_282,c_4])).

tff(c_80,plain,(
    ! [B_41,A_42] : k2_xboole_0(B_41,A_42) = k2_xboole_0(A_42,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_96,plain,(
    ! [A_42] : k2_xboole_0(k1_xboole_0,A_42) = A_42 ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_26])).

tff(c_321,plain,(
    ! [A_76,B_77] :
      ( k4_xboole_0(k2_xboole_0(A_76,B_77),B_77) = A_76
      | ~ r1_xboole_0(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_362,plain,(
    ! [A_78] :
      ( k4_xboole_0(A_78,A_78) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_321])).

tff(c_368,plain,(
    ! [B_66] :
      ( k4_xboole_0(B_66,B_66) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_286,c_362])).

tff(c_372,plain,(
    ! [B_66] : k4_xboole_0(B_66,B_66) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_368])).

tff(c_22,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_204,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_208,plain,(
    ! [B_15] : k3_xboole_0(B_15,B_15) = B_15 ),
    inference(resolution,[status(thm)],[c_22,c_204])).

tff(c_300,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_309,plain,(
    ! [B_15] : k5_xboole_0(B_15,B_15) = k4_xboole_0(B_15,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_300])).

tff(c_374,plain,(
    ! [B_15] : k5_xboole_0(B_15,B_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_309])).

tff(c_209,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k1_tarski(A_53),B_54)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_533,plain,(
    ! [A_93,B_94] :
      ( k3_xboole_0(k1_tarski(A_93),B_94) = k1_tarski(A_93)
      | ~ r2_hidden(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_209,c_28])).

tff(c_24,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_539,plain,(
    ! [A_93,B_94] :
      ( k5_xboole_0(k1_tarski(A_93),k1_tarski(A_93)) = k4_xboole_0(k1_tarski(A_93),B_94)
      | ~ r2_hidden(A_93,B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_24])).

tff(c_560,plain,(
    ! [A_95,B_96] :
      ( k4_xboole_0(k1_tarski(A_95),B_96) = k1_xboole_0
      | ~ r2_hidden(A_95,B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_539])).

tff(c_30,plain,(
    ! [A_21,B_22] : k2_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_574,plain,(
    ! [B_96,A_95] :
      ( k2_xboole_0(B_96,k1_tarski(A_95)) = k2_xboole_0(B_96,k1_xboole_0)
      | ~ r2_hidden(A_95,B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_30])).

tff(c_612,plain,(
    ! [B_98,A_99] :
      ( k2_xboole_0(B_98,k1_tarski(A_99)) = B_98
      | ~ r2_hidden(A_99,B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_574])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_50,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_638,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_50])).

tff(c_666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_638])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:22:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.33  
% 2.35/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.67/1.33  
% 2.67/1.33  %Foreground sorts:
% 2.67/1.33  
% 2.67/1.33  
% 2.67/1.33  %Background operators:
% 2.67/1.33  
% 2.67/1.33  
% 2.67/1.33  %Foreground operators:
% 2.67/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.67/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.67/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.67/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.67/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.67/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.67/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.67/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.67/1.33  
% 2.67/1.34  tff(f_93, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.67/1.34  tff(f_66, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.67/1.34  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.67/1.34  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.67/1.34  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.67/1.34  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.67/1.34  tff(f_76, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 2.67/1.34  tff(f_62, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.67/1.34  tff(f_70, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.67/1.34  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.67/1.34  tff(f_86, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.67/1.34  tff(f_72, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.67/1.34  tff(c_48, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.34  tff(c_26, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.67/1.34  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.67/1.34  tff(c_282, plain, (![A_65, B_66]: (r2_hidden('#skF_2'(A_65, B_66), A_65) | r1_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.67/1.34  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.34  tff(c_286, plain, (![A_65, B_66]: (~v1_xboole_0(A_65) | r1_xboole_0(A_65, B_66))), inference(resolution, [status(thm)], [c_282, c_4])).
% 2.67/1.34  tff(c_80, plain, (![B_41, A_42]: (k2_xboole_0(B_41, A_42)=k2_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.34  tff(c_96, plain, (![A_42]: (k2_xboole_0(k1_xboole_0, A_42)=A_42)), inference(superposition, [status(thm), theory('equality')], [c_80, c_26])).
% 2.67/1.34  tff(c_321, plain, (![A_76, B_77]: (k4_xboole_0(k2_xboole_0(A_76, B_77), B_77)=A_76 | ~r1_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.67/1.34  tff(c_362, plain, (![A_78]: (k4_xboole_0(A_78, A_78)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_78))), inference(superposition, [status(thm), theory('equality')], [c_96, c_321])).
% 2.67/1.34  tff(c_368, plain, (![B_66]: (k4_xboole_0(B_66, B_66)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_286, c_362])).
% 2.67/1.34  tff(c_372, plain, (![B_66]: (k4_xboole_0(B_66, B_66)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_368])).
% 2.67/1.34  tff(c_22, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.67/1.34  tff(c_204, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.67/1.34  tff(c_208, plain, (![B_15]: (k3_xboole_0(B_15, B_15)=B_15)), inference(resolution, [status(thm)], [c_22, c_204])).
% 2.67/1.34  tff(c_300, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.67/1.34  tff(c_309, plain, (![B_15]: (k5_xboole_0(B_15, B_15)=k4_xboole_0(B_15, B_15))), inference(superposition, [status(thm), theory('equality')], [c_208, c_300])).
% 2.67/1.34  tff(c_374, plain, (![B_15]: (k5_xboole_0(B_15, B_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_372, c_309])).
% 2.67/1.34  tff(c_209, plain, (![A_53, B_54]: (r1_tarski(k1_tarski(A_53), B_54) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.67/1.34  tff(c_28, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.67/1.34  tff(c_533, plain, (![A_93, B_94]: (k3_xboole_0(k1_tarski(A_93), B_94)=k1_tarski(A_93) | ~r2_hidden(A_93, B_94))), inference(resolution, [status(thm)], [c_209, c_28])).
% 2.67/1.34  tff(c_24, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.67/1.34  tff(c_539, plain, (![A_93, B_94]: (k5_xboole_0(k1_tarski(A_93), k1_tarski(A_93))=k4_xboole_0(k1_tarski(A_93), B_94) | ~r2_hidden(A_93, B_94))), inference(superposition, [status(thm), theory('equality')], [c_533, c_24])).
% 2.67/1.34  tff(c_560, plain, (![A_95, B_96]: (k4_xboole_0(k1_tarski(A_95), B_96)=k1_xboole_0 | ~r2_hidden(A_95, B_96))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_539])).
% 2.67/1.34  tff(c_30, plain, (![A_21, B_22]: (k2_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.67/1.34  tff(c_574, plain, (![B_96, A_95]: (k2_xboole_0(B_96, k1_tarski(A_95))=k2_xboole_0(B_96, k1_xboole_0) | ~r2_hidden(A_95, B_96))), inference(superposition, [status(thm), theory('equality')], [c_560, c_30])).
% 2.67/1.34  tff(c_612, plain, (![B_98, A_99]: (k2_xboole_0(B_98, k1_tarski(A_99))=B_98 | ~r2_hidden(A_99, B_98))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_574])).
% 2.67/1.34  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.34  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.67/1.34  tff(c_50, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 2.67/1.34  tff(c_638, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_612, c_50])).
% 2.67/1.34  tff(c_666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_638])).
% 2.67/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.34  
% 2.67/1.34  Inference rules
% 2.67/1.34  ----------------------
% 2.67/1.34  #Ref     : 0
% 2.67/1.34  #Sup     : 137
% 2.67/1.34  #Fact    : 0
% 2.67/1.34  #Define  : 0
% 2.67/1.34  #Split   : 0
% 2.67/1.34  #Chain   : 0
% 2.67/1.34  #Close   : 0
% 2.67/1.34  
% 2.67/1.34  Ordering : KBO
% 2.67/1.34  
% 2.67/1.34  Simplification rules
% 2.67/1.34  ----------------------
% 2.67/1.34  #Subsume      : 13
% 2.67/1.34  #Demod        : 40
% 2.67/1.34  #Tautology    : 88
% 2.67/1.34  #SimpNegUnit  : 0
% 2.67/1.34  #BackRed      : 2
% 2.67/1.34  
% 2.67/1.34  #Partial instantiations: 0
% 2.67/1.34  #Strategies tried      : 1
% 2.67/1.34  
% 2.67/1.34  Timing (in seconds)
% 2.67/1.34  ----------------------
% 2.67/1.35  Preprocessing        : 0.32
% 2.67/1.35  Parsing              : 0.17
% 2.67/1.35  CNF conversion       : 0.02
% 2.67/1.35  Main loop            : 0.26
% 2.67/1.35  Inferencing          : 0.10
% 2.67/1.35  Reduction            : 0.08
% 2.67/1.35  Demodulation         : 0.06
% 2.67/1.35  BG Simplification    : 0.02
% 2.67/1.35  Subsumption          : 0.04
% 2.67/1.35  Abstraction          : 0.02
% 2.67/1.35  MUC search           : 0.00
% 2.67/1.35  Cooper               : 0.00
% 2.67/1.35  Total                : 0.60
% 2.67/1.35  Index Insertion      : 0.00
% 2.67/1.35  Index Deletion       : 0.00
% 2.67/1.35  Index Matching       : 0.00
% 2.67/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
