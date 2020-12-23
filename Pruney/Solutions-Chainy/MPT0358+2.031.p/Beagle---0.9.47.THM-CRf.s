%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:04 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   57 (  95 expanded)
%              Number of leaves         :   34 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 ( 120 expanded)
%              Number of equality atoms :   18 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_102,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_106,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_54,plain,(
    ! [A_63] : k1_subset_1(A_63) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_60,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_67,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_60])).

tff(c_173,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_66,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_68,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_66])).

tff(c_242,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_68])).

tff(c_30,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_247,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_242,c_30])).

tff(c_451,plain,(
    ! [A_103,B_104,C_105] :
      ( ~ r1_xboole_0(A_103,B_104)
      | ~ r2_hidden(C_105,B_104)
      | ~ r2_hidden(C_105,A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_455,plain,(
    ! [C_106] : ~ r2_hidden(C_106,'#skF_4') ),
    inference(resolution,[status(thm)],[c_247,c_451])).

tff(c_470,plain,(
    ! [B_4] : r1_tarski('#skF_4',B_4) ),
    inference(resolution,[status(thm)],[c_8,c_455])).

tff(c_504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_173])).

tff(c_505,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_554,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_505,c_68])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_739,plain,(
    ! [A_148,B_149] :
      ( k4_xboole_0(A_148,B_149) = k3_subset_1(A_148,B_149)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(A_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_743,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_739])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k4_xboole_0(B_20,A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_757,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_743,c_22])).

tff(c_761,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_757])).

tff(c_763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_505,c_761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.41  
% 2.86/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.86/1.41  
% 2.86/1.41  %Foreground sorts:
% 2.86/1.41  
% 2.86/1.41  
% 2.86/1.41  %Background operators:
% 2.86/1.41  
% 2.86/1.41  
% 2.86/1.41  %Foreground operators:
% 2.86/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.86/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.86/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.86/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.86/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.86/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.86/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.86/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.86/1.41  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.86/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.86/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.86/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.86/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.41  
% 2.86/1.42  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.86/1.42  tff(f_102, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.86/1.42  tff(f_113, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.86/1.42  tff(f_80, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.86/1.42  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.86/1.42  tff(f_106, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.86/1.42  tff(f_62, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.86/1.42  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.86/1.42  tff(c_54, plain, (![A_63]: (k1_subset_1(A_63)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.86/1.42  tff(c_60, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.86/1.42  tff(c_67, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_60])).
% 2.86/1.42  tff(c_173, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_67])).
% 2.86/1.42  tff(c_66, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.86/1.42  tff(c_68, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_66])).
% 2.86/1.42  tff(c_242, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_173, c_68])).
% 2.86/1.42  tff(c_30, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.86/1.42  tff(c_247, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_242, c_30])).
% 2.86/1.42  tff(c_451, plain, (![A_103, B_104, C_105]: (~r1_xboole_0(A_103, B_104) | ~r2_hidden(C_105, B_104) | ~r2_hidden(C_105, A_103))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.86/1.42  tff(c_455, plain, (![C_106]: (~r2_hidden(C_106, '#skF_4'))), inference(resolution, [status(thm)], [c_247, c_451])).
% 2.86/1.42  tff(c_470, plain, (![B_4]: (r1_tarski('#skF_4', B_4))), inference(resolution, [status(thm)], [c_8, c_455])).
% 2.86/1.42  tff(c_504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_470, c_173])).
% 2.86/1.42  tff(c_505, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_67])).
% 2.86/1.42  tff(c_554, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_505, c_68])).
% 2.86/1.42  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.86/1.42  tff(c_739, plain, (![A_148, B_149]: (k4_xboole_0(A_148, B_149)=k3_subset_1(A_148, B_149) | ~m1_subset_1(B_149, k1_zfmisc_1(A_148)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.86/1.42  tff(c_743, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_739])).
% 2.86/1.42  tff(c_22, plain, (![A_19, B_20]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k4_xboole_0(B_20, A_19)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.86/1.42  tff(c_757, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_743, c_22])).
% 2.86/1.42  tff(c_761, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_554, c_757])).
% 2.86/1.42  tff(c_763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_505, c_761])).
% 2.86/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.42  
% 2.86/1.42  Inference rules
% 2.86/1.42  ----------------------
% 2.86/1.42  #Ref     : 0
% 2.86/1.42  #Sup     : 149
% 2.86/1.42  #Fact    : 0
% 2.86/1.42  #Define  : 0
% 2.86/1.42  #Split   : 1
% 2.86/1.42  #Chain   : 0
% 2.86/1.42  #Close   : 0
% 2.86/1.42  
% 2.86/1.42  Ordering : KBO
% 2.86/1.42  
% 2.86/1.42  Simplification rules
% 2.86/1.42  ----------------------
% 2.86/1.42  #Subsume      : 8
% 2.86/1.42  #Demod        : 47
% 2.86/1.42  #Tautology    : 121
% 2.86/1.42  #SimpNegUnit  : 3
% 2.86/1.42  #BackRed      : 7
% 2.86/1.42  
% 2.86/1.42  #Partial instantiations: 0
% 2.86/1.42  #Strategies tried      : 1
% 2.86/1.42  
% 2.86/1.42  Timing (in seconds)
% 2.86/1.42  ----------------------
% 2.86/1.42  Preprocessing        : 0.37
% 2.86/1.42  Parsing              : 0.20
% 2.86/1.42  CNF conversion       : 0.02
% 2.86/1.42  Main loop            : 0.29
% 2.86/1.42  Inferencing          : 0.10
% 2.86/1.42  Reduction            : 0.10
% 2.86/1.42  Demodulation         : 0.07
% 2.86/1.42  BG Simplification    : 0.02
% 2.86/1.42  Subsumption          : 0.04
% 2.86/1.42  Abstraction          : 0.02
% 2.86/1.42  MUC search           : 0.00
% 2.86/1.42  Cooper               : 0.00
% 2.86/1.42  Total                : 0.68
% 2.86/1.42  Index Insertion      : 0.00
% 2.86/1.42  Index Deletion       : 0.00
% 2.86/1.42  Index Matching       : 0.00
% 2.86/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
