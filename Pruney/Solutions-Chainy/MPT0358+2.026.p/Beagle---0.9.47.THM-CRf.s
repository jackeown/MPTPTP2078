%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:03 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 106 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   68 ( 147 expanded)
%              Number of equality atoms :   22 (  54 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_56,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_58,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_22,plain,(
    ! [A_20] : k1_subset_1(A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_35,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28])).

tff(c_79,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_35])).

tff(c_34,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_34])).

tff(c_80,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_36])).

tff(c_18,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_81,plain,(
    ! [A_17] : r1_tarski('#skF_4',A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_18])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_79])).

tff(c_90,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_35])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_91,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_35])).

tff(c_97,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = A_29
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_104,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_91,c_97])).

tff(c_192,plain,(
    ! [A_37,B_38,C_39] :
      ( ~ r1_xboole_0(A_37,B_38)
      | ~ r2_hidden(C_39,k3_xboole_0(A_37,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_195,plain,(
    ! [C_39] :
      ( ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4'))
      | ~ r2_hidden(C_39,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_192])).

tff(c_348,plain,(
    ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_609,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(A_80,B_81) = k3_subset_1(A_80,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_613,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_609])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_509,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_2'(A_70,B_71),k3_xboole_0(A_70,B_71))
      | r1_xboole_0(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_204,plain,(
    ! [A_1,B_2,C_39] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_39,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_192])).

tff(c_552,plain,(
    ! [B_74,A_75] :
      ( ~ r1_xboole_0(B_74,A_75)
      | r1_xboole_0(A_75,B_74) ) ),
    inference(resolution,[status(thm)],[c_509,c_204])).

tff(c_569,plain,(
    ! [B_19,A_18] : r1_xboole_0(B_19,k4_xboole_0(A_18,B_19)) ),
    inference(resolution,[status(thm)],[c_20,c_552])).

tff(c_618,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_569])).

tff(c_625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_348,c_618])).

tff(c_628,plain,(
    ! [C_82] : ~ r2_hidden(C_82,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_635,plain,(
    ! [B_83] : r1_tarski('#skF_4',B_83) ),
    inference(resolution,[status(thm)],[c_8,c_628])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_641,plain,(
    ! [B_84] : k3_xboole_0('#skF_4',B_84) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_635,c_16])).

tff(c_106,plain,(
    ! [A_31] : k3_xboole_0(k1_xboole_0,A_31) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_97])).

tff(c_111,plain,(
    ! [A_31] : k3_xboole_0(A_31,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_2])).

tff(c_656,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_641,c_111])).

tff(c_683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.33  
% 2.48/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.48/1.34  
% 2.48/1.34  %Foreground sorts:
% 2.48/1.34  
% 2.48/1.34  
% 2.48/1.34  %Background operators:
% 2.48/1.34  
% 2.48/1.34  
% 2.48/1.34  %Foreground operators:
% 2.48/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.48/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.34  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.48/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.48/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.48/1.34  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.48/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.48/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.48/1.34  
% 2.48/1.35  tff(f_60, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.48/1.35  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.48/1.35  tff(f_56, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.48/1.35  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.48/1.35  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.48/1.35  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.48/1.35  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.48/1.35  tff(f_58, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.48/1.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.48/1.35  tff(c_22, plain, (![A_20]: (k1_subset_1(A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.48/1.35  tff(c_28, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.48/1.35  tff(c_35, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_28])).
% 2.48/1.35  tff(c_79, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_35])).
% 2.48/1.35  tff(c_34, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.48/1.35  tff(c_36, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_34])).
% 2.48/1.35  tff(c_80, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_79, c_36])).
% 2.48/1.35  tff(c_18, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.48/1.35  tff(c_81, plain, (![A_17]: (r1_tarski('#skF_4', A_17))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_18])).
% 2.48/1.35  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_79])).
% 2.48/1.35  tff(c_90, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_35])).
% 2.48/1.35  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.48/1.35  tff(c_91, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_35])).
% 2.48/1.35  tff(c_97, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=A_29 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.48/1.35  tff(c_104, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_91, c_97])).
% 2.48/1.35  tff(c_192, plain, (![A_37, B_38, C_39]: (~r1_xboole_0(A_37, B_38) | ~r2_hidden(C_39, k3_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.48/1.35  tff(c_195, plain, (![C_39]: (~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | ~r2_hidden(C_39, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_104, c_192])).
% 2.48/1.35  tff(c_348, plain, (~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_195])).
% 2.48/1.35  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.48/1.35  tff(c_609, plain, (![A_80, B_81]: (k4_xboole_0(A_80, B_81)=k3_subset_1(A_80, B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.48/1.35  tff(c_613, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_609])).
% 2.48/1.35  tff(c_20, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.48/1.35  tff(c_509, plain, (![A_70, B_71]: (r2_hidden('#skF_2'(A_70, B_71), k3_xboole_0(A_70, B_71)) | r1_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.48/1.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.35  tff(c_204, plain, (![A_1, B_2, C_39]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_39, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_192])).
% 2.48/1.35  tff(c_552, plain, (![B_74, A_75]: (~r1_xboole_0(B_74, A_75) | r1_xboole_0(A_75, B_74))), inference(resolution, [status(thm)], [c_509, c_204])).
% 2.48/1.35  tff(c_569, plain, (![B_19, A_18]: (r1_xboole_0(B_19, k4_xboole_0(A_18, B_19)))), inference(resolution, [status(thm)], [c_20, c_552])).
% 2.48/1.35  tff(c_618, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_613, c_569])).
% 2.48/1.35  tff(c_625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_348, c_618])).
% 2.48/1.35  tff(c_628, plain, (![C_82]: (~r2_hidden(C_82, '#skF_4'))), inference(splitRight, [status(thm)], [c_195])).
% 2.48/1.35  tff(c_635, plain, (![B_83]: (r1_tarski('#skF_4', B_83))), inference(resolution, [status(thm)], [c_8, c_628])).
% 2.48/1.35  tff(c_16, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.48/1.35  tff(c_641, plain, (![B_84]: (k3_xboole_0('#skF_4', B_84)='#skF_4')), inference(resolution, [status(thm)], [c_635, c_16])).
% 2.48/1.35  tff(c_106, plain, (![A_31]: (k3_xboole_0(k1_xboole_0, A_31)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_97])).
% 2.48/1.35  tff(c_111, plain, (![A_31]: (k3_xboole_0(A_31, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_106, c_2])).
% 2.48/1.35  tff(c_656, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_641, c_111])).
% 2.48/1.35  tff(c_683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_656])).
% 2.48/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.35  
% 2.48/1.35  Inference rules
% 2.48/1.35  ----------------------
% 2.48/1.35  #Ref     : 0
% 2.48/1.35  #Sup     : 172
% 2.48/1.35  #Fact    : 0
% 2.48/1.35  #Define  : 0
% 2.48/1.35  #Split   : 5
% 2.48/1.35  #Chain   : 0
% 2.48/1.35  #Close   : 0
% 2.48/1.35  
% 2.48/1.35  Ordering : KBO
% 2.48/1.35  
% 2.48/1.35  Simplification rules
% 2.48/1.35  ----------------------
% 2.48/1.35  #Subsume      : 36
% 2.48/1.35  #Demod        : 50
% 2.48/1.35  #Tautology    : 86
% 2.48/1.35  #SimpNegUnit  : 7
% 2.48/1.35  #BackRed      : 5
% 2.48/1.35  
% 2.48/1.35  #Partial instantiations: 0
% 2.48/1.35  #Strategies tried      : 1
% 2.48/1.35  
% 2.48/1.35  Timing (in seconds)
% 2.48/1.35  ----------------------
% 2.48/1.35  Preprocessing        : 0.30
% 2.48/1.35  Parsing              : 0.16
% 2.48/1.35  CNF conversion       : 0.02
% 2.48/1.35  Main loop            : 0.28
% 2.48/1.35  Inferencing          : 0.10
% 2.48/1.35  Reduction            : 0.10
% 2.48/1.35  Demodulation         : 0.07
% 2.48/1.35  BG Simplification    : 0.01
% 2.48/1.36  Subsumption          : 0.04
% 2.48/1.36  Abstraction          : 0.02
% 2.48/1.36  MUC search           : 0.00
% 2.48/1.36  Cooper               : 0.00
% 2.48/1.36  Total                : 0.61
% 2.48/1.36  Index Insertion      : 0.00
% 2.48/1.36  Index Deletion       : 0.00
% 2.48/1.36  Index Matching       : 0.00
% 2.48/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
