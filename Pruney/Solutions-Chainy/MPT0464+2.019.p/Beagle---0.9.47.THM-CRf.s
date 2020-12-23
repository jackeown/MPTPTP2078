%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:45 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 112 expanded)
%              Number of leaves         :   31 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :   92 ( 194 expanded)
%              Number of equality atoms :   12 (  33 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_59,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_56,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    ! [A_73,B_74,C_75] : k2_enumset1(A_73,A_73,B_74,C_75) = k1_enumset1(A_73,B_74,C_75) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [F_22,A_15,B_16,C_17] : r2_hidden(F_22,k2_enumset1(A_15,B_16,C_17,F_22)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_135,plain,(
    ! [C_87,A_88,B_89] : r2_hidden(C_87,k1_enumset1(A_88,B_89,C_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_14])).

tff(c_138,plain,(
    ! [B_7,A_6] : r2_hidden(B_7,k2_tarski(A_6,B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_135])).

tff(c_48,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k1_setfam_1(B_28),A_27)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_46,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(A_25,k1_zfmisc_1(B_26))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_94,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_141,plain,(
    ! [A_92,B_93] :
      ( v1_relat_1(A_92)
      | ~ v1_relat_1(B_93)
      | ~ r1_tarski(A_92,B_93) ) ),
    inference(resolution,[status(thm)],[c_46,c_94])).

tff(c_164,plain,(
    ! [B_100,A_101] :
      ( v1_relat_1(k1_setfam_1(B_100))
      | ~ v1_relat_1(A_101)
      | ~ r2_hidden(A_101,B_100) ) ),
    inference(resolution,[status(thm)],[c_48,c_141])).

tff(c_166,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(A_6,B_7)))
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_138,c_164])).

tff(c_184,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k3_xboole_0(A_6,B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_166])).

tff(c_60,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_80,plain,(
    ! [A_61,B_62] : k1_setfam_1(k2_tarski(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_339,plain,(
    ! [A_167,B_168,A_169] :
      ( r1_tarski(k3_xboole_0(A_167,B_168),A_169)
      | ~ r2_hidden(A_169,k2_tarski(A_167,B_168)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_48])).

tff(c_346,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),B_7) ),
    inference(resolution,[status(thm)],[c_138,c_339])).

tff(c_361,plain,(
    ! [C_175,A_176,B_177] :
      ( r1_tarski(k5_relat_1(C_175,A_176),k5_relat_1(C_175,B_177))
      | ~ r1_tarski(A_176,B_177)
      | ~ v1_relat_1(C_175)
      | ~ v1_relat_1(B_177)
      | ~ v1_relat_1(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_261,plain,(
    ! [C_137,A_138,B_139] :
      ( r1_tarski(k5_relat_1(C_137,A_138),k5_relat_1(C_137,B_139))
      | ~ r1_tarski(A_138,B_139)
      | ~ v1_relat_1(C_137)
      | ~ v1_relat_1(B_139)
      | ~ v1_relat_1(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_130,plain,(
    ! [A_84,B_85,C_86] :
      ( r1_tarski(A_84,k3_xboole_0(B_85,C_86))
      | ~ r1_tarski(A_84,C_86)
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k5_relat_1('#skF_3','#skF_4'),k5_relat_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_134,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_130,c_54])).

tff(c_200,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_264,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_261,c_200])).

tff(c_270,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_2,c_264])).

tff(c_274,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_184,c_270])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_274])).

tff(c_282,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_364,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_361,c_282])).

tff(c_370,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_346,c_364])).

tff(c_374,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_184,c_370])).

tff(c_381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_374])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:56:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.37  
% 2.47/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.37  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 2.47/1.37  
% 2.47/1.37  %Foreground sorts:
% 2.47/1.37  
% 2.47/1.37  
% 2.47/1.37  %Background operators:
% 2.47/1.37  
% 2.47/1.37  
% 2.47/1.37  %Foreground operators:
% 2.47/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.47/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.47/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.47/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.47/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.47/1.37  
% 2.87/1.39  tff(f_97, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 2.87/1.39  tff(f_59, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.87/1.39  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.87/1.39  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.87/1.39  tff(f_57, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 2.87/1.39  tff(f_67, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.87/1.39  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.87/1.39  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.87/1.39  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 2.87/1.39  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.87/1.39  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.87/1.39  tff(c_56, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.87/1.39  tff(c_42, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.87/1.39  tff(c_6, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.87/1.39  tff(c_99, plain, (![A_73, B_74, C_75]: (k2_enumset1(A_73, A_73, B_74, C_75)=k1_enumset1(A_73, B_74, C_75))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.87/1.39  tff(c_14, plain, (![F_22, A_15, B_16, C_17]: (r2_hidden(F_22, k2_enumset1(A_15, B_16, C_17, F_22)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.87/1.39  tff(c_135, plain, (![C_87, A_88, B_89]: (r2_hidden(C_87, k1_enumset1(A_88, B_89, C_87)))), inference(superposition, [status(thm), theory('equality')], [c_99, c_14])).
% 2.87/1.39  tff(c_138, plain, (![B_7, A_6]: (r2_hidden(B_7, k2_tarski(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_135])).
% 2.87/1.39  tff(c_48, plain, (![B_28, A_27]: (r1_tarski(k1_setfam_1(B_28), A_27) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.87/1.39  tff(c_46, plain, (![A_25, B_26]: (m1_subset_1(A_25, k1_zfmisc_1(B_26)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.87/1.39  tff(c_94, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.87/1.39  tff(c_141, plain, (![A_92, B_93]: (v1_relat_1(A_92) | ~v1_relat_1(B_93) | ~r1_tarski(A_92, B_93))), inference(resolution, [status(thm)], [c_46, c_94])).
% 2.87/1.39  tff(c_164, plain, (![B_100, A_101]: (v1_relat_1(k1_setfam_1(B_100)) | ~v1_relat_1(A_101) | ~r2_hidden(A_101, B_100))), inference(resolution, [status(thm)], [c_48, c_141])).
% 2.87/1.39  tff(c_166, plain, (![A_6, B_7]: (v1_relat_1(k1_setfam_1(k2_tarski(A_6, B_7))) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_138, c_164])).
% 2.87/1.39  tff(c_184, plain, (![A_6, B_7]: (v1_relat_1(k3_xboole_0(A_6, B_7)) | ~v1_relat_1(B_7))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_166])).
% 2.87/1.39  tff(c_60, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.87/1.39  tff(c_80, plain, (![A_61, B_62]: (k1_setfam_1(k2_tarski(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.87/1.39  tff(c_339, plain, (![A_167, B_168, A_169]: (r1_tarski(k3_xboole_0(A_167, B_168), A_169) | ~r2_hidden(A_169, k2_tarski(A_167, B_168)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_48])).
% 2.87/1.39  tff(c_346, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), B_7))), inference(resolution, [status(thm)], [c_138, c_339])).
% 2.87/1.39  tff(c_361, plain, (![C_175, A_176, B_177]: (r1_tarski(k5_relat_1(C_175, A_176), k5_relat_1(C_175, B_177)) | ~r1_tarski(A_176, B_177) | ~v1_relat_1(C_175) | ~v1_relat_1(B_177) | ~v1_relat_1(A_176))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.87/1.39  tff(c_58, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.87/1.39  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.87/1.39  tff(c_261, plain, (![C_137, A_138, B_139]: (r1_tarski(k5_relat_1(C_137, A_138), k5_relat_1(C_137, B_139)) | ~r1_tarski(A_138, B_139) | ~v1_relat_1(C_137) | ~v1_relat_1(B_139) | ~v1_relat_1(A_138))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.87/1.39  tff(c_130, plain, (![A_84, B_85, C_86]: (r1_tarski(A_84, k3_xboole_0(B_85, C_86)) | ~r1_tarski(A_84, C_86) | ~r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.39  tff(c_54, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k5_relat_1('#skF_3', '#skF_4'), k5_relat_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.87/1.39  tff(c_134, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5')) | ~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_130, c_54])).
% 2.87/1.39  tff(c_200, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_134])).
% 2.87/1.39  tff(c_264, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_261, c_200])).
% 2.87/1.39  tff(c_270, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_2, c_264])).
% 2.87/1.39  tff(c_274, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_184, c_270])).
% 2.87/1.39  tff(c_281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_274])).
% 2.87/1.39  tff(c_282, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_134])).
% 2.87/1.39  tff(c_364, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_361, c_282])).
% 2.87/1.39  tff(c_370, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_346, c_364])).
% 2.87/1.39  tff(c_374, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_184, c_370])).
% 2.87/1.39  tff(c_381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_374])).
% 2.87/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.39  
% 2.87/1.39  Inference rules
% 2.87/1.39  ----------------------
% 2.87/1.39  #Ref     : 0
% 2.87/1.39  #Sup     : 70
% 2.87/1.39  #Fact    : 0
% 2.87/1.39  #Define  : 0
% 2.87/1.39  #Split   : 2
% 2.87/1.39  #Chain   : 0
% 2.87/1.39  #Close   : 0
% 2.87/1.39  
% 2.87/1.39  Ordering : KBO
% 2.87/1.39  
% 2.87/1.39  Simplification rules
% 2.87/1.39  ----------------------
% 2.87/1.39  #Subsume      : 17
% 2.87/1.39  #Demod        : 19
% 2.87/1.39  #Tautology    : 21
% 2.87/1.39  #SimpNegUnit  : 0
% 2.87/1.39  #BackRed      : 0
% 2.87/1.39  
% 2.87/1.39  #Partial instantiations: 0
% 2.87/1.39  #Strategies tried      : 1
% 2.87/1.39  
% 2.87/1.39  Timing (in seconds)
% 2.87/1.39  ----------------------
% 2.87/1.39  Preprocessing        : 0.34
% 2.87/1.39  Parsing              : 0.17
% 2.87/1.39  CNF conversion       : 0.03
% 2.87/1.39  Main loop            : 0.27
% 2.87/1.39  Inferencing          : 0.10
% 2.87/1.39  Reduction            : 0.08
% 2.87/1.39  Demodulation         : 0.06
% 2.87/1.39  BG Simplification    : 0.02
% 2.87/1.39  Subsumption          : 0.06
% 2.87/1.39  Abstraction          : 0.02
% 2.87/1.39  MUC search           : 0.00
% 2.87/1.39  Cooper               : 0.00
% 2.87/1.39  Total                : 0.64
% 2.87/1.39  Index Insertion      : 0.00
% 2.87/1.39  Index Deletion       : 0.00
% 2.87/1.39  Index Matching       : 0.00
% 2.87/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
