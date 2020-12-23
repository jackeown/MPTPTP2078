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
% DateTime   : Thu Dec  3 09:55:38 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   58 (  67 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  72 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_50,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_48,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    ! [A_21] : k2_subset_1(A_21) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [A_22] : m1_subset_1(k2_subset_1(A_22),k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_33,plain,(
    ! [A_22] : m1_subset_1(A_22,k1_zfmisc_1(A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_290,plain,(
    ! [A_66,B_67,C_68] :
      ( k4_subset_1(A_66,B_67,C_68) = k2_xboole_0(B_67,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(A_66))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_329,plain,(
    ! [A_73,B_74] :
      ( k4_subset_1(A_73,B_74,A_73) = k2_xboole_0(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(resolution,[status(thm)],[c_33,c_290])).

tff(c_336,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_329])).

tff(c_30,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_30])).

tff(c_346,plain,(
    k2_xboole_0('#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_34])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_286,plain,(
    ! [C_63,A_64,B_65] :
      ( r2_hidden(C_63,A_64)
      | ~ r2_hidden(C_63,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_351,plain,(
    ! [A_76,B_77,A_78] :
      ( r2_hidden('#skF_1'(A_76,B_77),A_78)
      | ~ m1_subset_1(A_76,k1_zfmisc_1(A_78))
      | r1_tarski(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_8,c_286])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_363,plain,(
    ! [A_79,A_80] :
      ( ~ m1_subset_1(A_79,k1_zfmisc_1(A_80))
      | r1_tarski(A_79,A_80) ) ),
    inference(resolution,[status(thm)],[c_351,c_6])).

tff(c_372,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_363])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_376,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_372,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_111,plain,(
    ! [A_36,B_37] : k2_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_120,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_111])).

tff(c_380,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_120])).

tff(c_14,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_155,plain,(
    ! [A_42,B_43] : k3_tarski(k2_tarski(A_42,B_43)) = k2_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_179,plain,(
    ! [B_46,A_47] : k3_tarski(k2_tarski(B_46,A_47)) = k2_xboole_0(A_47,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_155])).

tff(c_20,plain,(
    ! [A_19,B_20] : k3_tarski(k2_tarski(A_19,B_20)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_185,plain,(
    ! [B_46,A_47] : k2_xboole_0(B_46,A_47) = k2_xboole_0(A_47,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_20])).

tff(c_391,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_185])).

tff(c_404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_346,c_391])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.28  
% 2.19/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.28  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.19/1.28  
% 2.19/1.28  %Foreground sorts:
% 2.19/1.28  
% 2.19/1.28  
% 2.19/1.28  %Background operators:
% 2.19/1.28  
% 2.19/1.28  
% 2.19/1.28  %Foreground operators:
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.28  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.19/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.28  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.19/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.28  
% 2.19/1.29  tff(f_70, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 2.19/1.29  tff(f_50, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.19/1.29  tff(f_52, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.19/1.29  tff(f_65, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.19/1.29  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.19/1.29  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.19/1.29  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.19/1.29  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.19/1.29  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.19/1.29  tff(f_42, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.19/1.29  tff(f_48, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.19/1.29  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.19/1.29  tff(c_22, plain, (![A_21]: (k2_subset_1(A_21)=A_21)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.19/1.29  tff(c_24, plain, (![A_22]: (m1_subset_1(k2_subset_1(A_22), k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.19/1.29  tff(c_33, plain, (![A_22]: (m1_subset_1(A_22, k1_zfmisc_1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 2.19/1.29  tff(c_290, plain, (![A_66, B_67, C_68]: (k4_subset_1(A_66, B_67, C_68)=k2_xboole_0(B_67, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(A_66)) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.19/1.29  tff(c_329, plain, (![A_73, B_74]: (k4_subset_1(A_73, B_74, A_73)=k2_xboole_0(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(resolution, [status(thm)], [c_33, c_290])).
% 2.19/1.29  tff(c_336, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_329])).
% 2.19/1.29  tff(c_30, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.19/1.29  tff(c_34, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_30])).
% 2.19/1.29  tff(c_346, plain, (k2_xboole_0('#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_336, c_34])).
% 2.19/1.29  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.19/1.29  tff(c_286, plain, (![C_63, A_64, B_65]: (r2_hidden(C_63, A_64) | ~r2_hidden(C_63, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.29  tff(c_351, plain, (![A_76, B_77, A_78]: (r2_hidden('#skF_1'(A_76, B_77), A_78) | ~m1_subset_1(A_76, k1_zfmisc_1(A_78)) | r1_tarski(A_76, B_77))), inference(resolution, [status(thm)], [c_8, c_286])).
% 2.19/1.29  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.19/1.29  tff(c_363, plain, (![A_79, A_80]: (~m1_subset_1(A_79, k1_zfmisc_1(A_80)) | r1_tarski(A_79, A_80))), inference(resolution, [status(thm)], [c_351, c_6])).
% 2.19/1.29  tff(c_372, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_363])).
% 2.19/1.29  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.19/1.29  tff(c_376, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_372, c_12])).
% 2.19/1.29  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.29  tff(c_111, plain, (![A_36, B_37]: (k2_xboole_0(A_36, k3_xboole_0(A_36, B_37))=A_36)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.19/1.29  tff(c_120, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_111])).
% 2.19/1.29  tff(c_380, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_376, c_120])).
% 2.19/1.29  tff(c_14, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.19/1.29  tff(c_155, plain, (![A_42, B_43]: (k3_tarski(k2_tarski(A_42, B_43))=k2_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.19/1.29  tff(c_179, plain, (![B_46, A_47]: (k3_tarski(k2_tarski(B_46, A_47))=k2_xboole_0(A_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_14, c_155])).
% 2.19/1.29  tff(c_20, plain, (![A_19, B_20]: (k3_tarski(k2_tarski(A_19, B_20))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.19/1.29  tff(c_185, plain, (![B_46, A_47]: (k2_xboole_0(B_46, A_47)=k2_xboole_0(A_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_179, c_20])).
% 2.19/1.29  tff(c_391, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_380, c_185])).
% 2.19/1.29  tff(c_404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_346, c_391])).
% 2.19/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.29  
% 2.19/1.29  Inference rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Ref     : 0
% 2.19/1.29  #Sup     : 93
% 2.19/1.29  #Fact    : 0
% 2.19/1.29  #Define  : 0
% 2.19/1.29  #Split   : 0
% 2.19/1.29  #Chain   : 0
% 2.19/1.29  #Close   : 0
% 2.19/1.29  
% 2.19/1.29  Ordering : KBO
% 2.19/1.29  
% 2.19/1.29  Simplification rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Subsume      : 1
% 2.19/1.29  #Demod        : 16
% 2.19/1.29  #Tautology    : 65
% 2.19/1.29  #SimpNegUnit  : 1
% 2.19/1.29  #BackRed      : 1
% 2.19/1.29  
% 2.19/1.29  #Partial instantiations: 0
% 2.19/1.29  #Strategies tried      : 1
% 2.19/1.29  
% 2.19/1.29  Timing (in seconds)
% 2.19/1.29  ----------------------
% 2.19/1.30  Preprocessing        : 0.31
% 2.19/1.30  Parsing              : 0.17
% 2.19/1.30  CNF conversion       : 0.02
% 2.19/1.30  Main loop            : 0.23
% 2.19/1.30  Inferencing          : 0.09
% 2.19/1.30  Reduction            : 0.08
% 2.19/1.30  Demodulation         : 0.06
% 2.19/1.30  BG Simplification    : 0.01
% 2.19/1.30  Subsumption          : 0.04
% 2.19/1.30  Abstraction          : 0.01
% 2.19/1.30  MUC search           : 0.00
% 2.19/1.30  Cooper               : 0.00
% 2.19/1.30  Total                : 0.57
% 2.19/1.30  Index Insertion      : 0.00
% 2.19/1.30  Index Deletion       : 0.00
% 2.19/1.30  Index Matching       : 0.00
% 2.19/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
