%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:04 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   58 (  96 expanded)
%              Number of leaves         :   35 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 ( 120 expanded)
%              Number of equality atoms :   18 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_104,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_54,axiom,(
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

tff(f_108,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    ! [A_63] : k1_subset_1(A_63) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_62,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_69,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_62])).

tff(c_137,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_68,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_70,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_68])).

tff(c_266,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_70])).

tff(c_28,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_271,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_266,c_28])).

tff(c_497,plain,(
    ! [A_111,B_112,C_113] :
      ( ~ r1_xboole_0(A_111,B_112)
      | ~ r2_hidden(C_113,B_112)
      | ~ r2_hidden(C_113,A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_501,plain,(
    ! [C_114] : ~ r2_hidden(C_114,'#skF_4') ),
    inference(resolution,[status(thm)],[c_271,c_497])).

tff(c_514,plain,(
    ! [B_4] : r1_tarski('#skF_4',B_4) ),
    inference(resolution,[status(thm)],[c_8,c_501])).

tff(c_519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_137])).

tff(c_520,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_522,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_520,c_70])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1011,plain,(
    ! [A_165,B_166] :
      ( k4_xboole_0(A_165,B_166) = k3_subset_1(A_165,B_166)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(A_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1015,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1011])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,k4_xboole_0(B_18,A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1019,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1015,c_20])).

tff(c_1023,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_1019])).

tff(c_1025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_520,c_1023])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.39  
% 2.71/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.71/1.39  
% 2.71/1.39  %Foreground sorts:
% 2.71/1.39  
% 2.71/1.39  
% 2.71/1.39  %Background operators:
% 2.71/1.39  
% 2.71/1.39  
% 2.71/1.39  %Foreground operators:
% 2.71/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.71/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.71/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.71/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.71/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.71/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.39  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.71/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.71/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.71/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.71/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.71/1.39  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.71/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.71/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.71/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.71/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.39  
% 2.71/1.40  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.71/1.40  tff(f_104, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.71/1.40  tff(f_115, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.71/1.40  tff(f_78, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.71/1.40  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.71/1.40  tff(f_108, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.71/1.40  tff(f_60, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.71/1.40  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.71/1.40  tff(c_56, plain, (![A_63]: (k1_subset_1(A_63)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.71/1.40  tff(c_62, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.71/1.40  tff(c_69, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_62])).
% 2.71/1.40  tff(c_137, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_69])).
% 2.71/1.40  tff(c_68, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.71/1.40  tff(c_70, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_68])).
% 2.71/1.40  tff(c_266, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_137, c_70])).
% 2.71/1.40  tff(c_28, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.71/1.40  tff(c_271, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_266, c_266, c_28])).
% 2.71/1.40  tff(c_497, plain, (![A_111, B_112, C_113]: (~r1_xboole_0(A_111, B_112) | ~r2_hidden(C_113, B_112) | ~r2_hidden(C_113, A_111))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.71/1.40  tff(c_501, plain, (![C_114]: (~r2_hidden(C_114, '#skF_4'))), inference(resolution, [status(thm)], [c_271, c_497])).
% 2.71/1.40  tff(c_514, plain, (![B_4]: (r1_tarski('#skF_4', B_4))), inference(resolution, [status(thm)], [c_8, c_501])).
% 2.71/1.40  tff(c_519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_514, c_137])).
% 2.71/1.40  tff(c_520, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_69])).
% 2.71/1.40  tff(c_522, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_520, c_70])).
% 2.71/1.40  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.71/1.40  tff(c_1011, plain, (![A_165, B_166]: (k4_xboole_0(A_165, B_166)=k3_subset_1(A_165, B_166) | ~m1_subset_1(B_166, k1_zfmisc_1(A_165)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.71/1.40  tff(c_1015, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_1011])).
% 2.71/1.40  tff(c_20, plain, (![A_17, B_18]: (k1_xboole_0=A_17 | ~r1_tarski(A_17, k4_xboole_0(B_18, A_17)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.71/1.40  tff(c_1019, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1015, c_20])).
% 2.71/1.40  tff(c_1023, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_522, c_1019])).
% 2.71/1.40  tff(c_1025, plain, $false, inference(negUnitSimplification, [status(thm)], [c_520, c_1023])).
% 2.71/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.40  
% 2.71/1.40  Inference rules
% 2.71/1.40  ----------------------
% 2.71/1.40  #Ref     : 0
% 2.71/1.40  #Sup     : 216
% 2.71/1.40  #Fact    : 0
% 2.71/1.40  #Define  : 0
% 2.71/1.40  #Split   : 1
% 2.71/1.40  #Chain   : 0
% 2.71/1.40  #Close   : 0
% 2.71/1.40  
% 2.71/1.40  Ordering : KBO
% 2.71/1.40  
% 2.71/1.40  Simplification rules
% 2.71/1.40  ----------------------
% 2.71/1.40  #Subsume      : 6
% 2.71/1.40  #Demod        : 84
% 2.71/1.40  #Tautology    : 160
% 2.71/1.40  #SimpNegUnit  : 3
% 2.71/1.40  #BackRed      : 7
% 2.71/1.40  
% 2.71/1.40  #Partial instantiations: 0
% 2.71/1.40  #Strategies tried      : 1
% 2.71/1.40  
% 2.71/1.40  Timing (in seconds)
% 2.71/1.40  ----------------------
% 2.71/1.40  Preprocessing        : 0.33
% 2.71/1.40  Parsing              : 0.18
% 2.71/1.40  CNF conversion       : 0.02
% 2.71/1.40  Main loop            : 0.31
% 2.71/1.40  Inferencing          : 0.11
% 2.71/1.40  Reduction            : 0.11
% 2.71/1.40  Demodulation         : 0.08
% 2.71/1.40  BG Simplification    : 0.02
% 2.71/1.40  Subsumption          : 0.04
% 2.71/1.40  Abstraction          : 0.02
% 2.71/1.40  MUC search           : 0.00
% 2.71/1.40  Cooper               : 0.00
% 2.71/1.40  Total                : 0.67
% 2.71/1.40  Index Insertion      : 0.00
% 2.71/1.40  Index Deletion       : 0.00
% 2.71/1.40  Index Matching       : 0.00
% 2.71/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
