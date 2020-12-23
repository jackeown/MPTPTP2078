%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:05 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   60 (  94 expanded)
%              Number of leaves         :   28 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 145 expanded)
%              Number of equality atoms :   22 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_74,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_68,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_50,axiom,(
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

tff(c_28,plain,(
    ! [A_21] : k1_subset_1(A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_34,plain,
    ( k1_subset_1('#skF_4') != '#skF_5'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_41,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_34])).

tff(c_54,plain,(
    ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_41])).

tff(c_40,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | k1_subset_1('#skF_4') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_40])).

tff(c_55,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_42])).

tff(c_24,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_57,plain,(
    ! [A_17] : r1_tarski('#skF_5',A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_24])).

tff(c_65,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_54])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_20,plain,(
    ! [B_14] : r1_tarski(B_14,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_68,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_69,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_68])).

tff(c_70,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_124,plain,(
    ! [C_47,B_48,A_49] :
      ( r2_hidden(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_137,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_3'(A_50),B_51)
      | ~ r1_tarski(A_50,B_51)
      | k1_xboole_0 = A_50 ) ),
    inference(resolution,[status(thm)],[c_14,c_124])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_242,plain,(
    ! [A_70,B_71,B_72] :
      ( r2_hidden('#skF_3'(A_70),B_71)
      | ~ r1_tarski(B_72,B_71)
      | ~ r1_tarski(A_70,B_72)
      | k1_xboole_0 = A_70 ) ),
    inference(resolution,[status(thm)],[c_137,c_2])).

tff(c_252,plain,(
    ! [A_73] :
      ( r2_hidden('#skF_3'(A_73),k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_73,'#skF_5')
      | k1_xboole_0 = A_73 ) ),
    inference(resolution,[status(thm)],[c_70,c_242])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_141,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = k3_subset_1(A_52,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_145,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_141])).

tff(c_26,plain,(
    ! [A_18,C_20,B_19] :
      ( r1_xboole_0(A_18,k4_xboole_0(C_20,B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_120,plain,(
    ! [A_44,B_45,C_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | ~ r2_hidden(C_46,B_45)
      | ~ r2_hidden(C_46,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_170,plain,(
    ! [C_61,C_62,B_63,A_64] :
      ( ~ r2_hidden(C_61,k4_xboole_0(C_62,B_63))
      | ~ r2_hidden(C_61,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(resolution,[status(thm)],[c_26,c_120])).

tff(c_178,plain,(
    ! [C_61,A_64] :
      ( ~ r2_hidden(C_61,k3_subset_1('#skF_4','#skF_5'))
      | ~ r2_hidden(C_61,A_64)
      | ~ r1_tarski(A_64,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_170])).

tff(c_259,plain,(
    ! [A_74,A_75] :
      ( ~ r2_hidden('#skF_3'(A_74),A_75)
      | ~ r1_tarski(A_75,'#skF_5')
      | ~ r1_tarski(A_74,'#skF_5')
      | k1_xboole_0 = A_74 ) ),
    inference(resolution,[status(thm)],[c_252,c_178])).

tff(c_272,plain,(
    ! [A_76] :
      ( ~ r1_tarski(A_76,'#skF_5')
      | k1_xboole_0 = A_76 ) ),
    inference(resolution,[status(thm)],[c_14,c_259])).

tff(c_280,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_20,c_272])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.28  
% 2.38/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.38/1.28  
% 2.38/1.28  %Foreground sorts:
% 2.38/1.28  
% 2.38/1.28  
% 2.38/1.28  %Background operators:
% 2.38/1.28  
% 2.38/1.28  
% 2.38/1.28  %Foreground operators:
% 2.38/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.38/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.38/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.38/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.38/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.38/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.28  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.38/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.38/1.28  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.38/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.38/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.38/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.28  
% 2.38/1.29  tff(f_74, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.38/1.29  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.38/1.29  tff(f_68, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.38/1.29  tff(f_64, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.38/1.29  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.38/1.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.38/1.29  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.38/1.29  tff(f_72, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.38/1.29  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.38/1.29  tff(c_28, plain, (![A_21]: (k1_subset_1(A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.38/1.29  tff(c_34, plain, (k1_subset_1('#skF_4')!='#skF_5' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.38/1.29  tff(c_41, plain, (k1_xboole_0!='#skF_5' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_34])).
% 2.38/1.29  tff(c_54, plain, (~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_41])).
% 2.38/1.29  tff(c_40, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | k1_subset_1('#skF_4')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.38/1.29  tff(c_42, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_40])).
% 2.38/1.29  tff(c_55, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_54, c_42])).
% 2.38/1.29  tff(c_24, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.38/1.29  tff(c_57, plain, (![A_17]: (r1_tarski('#skF_5', A_17))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_24])).
% 2.38/1.29  tff(c_65, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_54])).
% 2.38/1.29  tff(c_66, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_41])).
% 2.38/1.29  tff(c_20, plain, (![B_14]: (r1_tarski(B_14, B_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.38/1.29  tff(c_14, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.38/1.29  tff(c_68, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_42])).
% 2.38/1.29  tff(c_69, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_68])).
% 2.38/1.29  tff(c_70, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_42])).
% 2.38/1.29  tff(c_124, plain, (![C_47, B_48, A_49]: (r2_hidden(C_47, B_48) | ~r2_hidden(C_47, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.38/1.29  tff(c_137, plain, (![A_50, B_51]: (r2_hidden('#skF_3'(A_50), B_51) | ~r1_tarski(A_50, B_51) | k1_xboole_0=A_50)), inference(resolution, [status(thm)], [c_14, c_124])).
% 2.38/1.29  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.38/1.29  tff(c_242, plain, (![A_70, B_71, B_72]: (r2_hidden('#skF_3'(A_70), B_71) | ~r1_tarski(B_72, B_71) | ~r1_tarski(A_70, B_72) | k1_xboole_0=A_70)), inference(resolution, [status(thm)], [c_137, c_2])).
% 2.38/1.29  tff(c_252, plain, (![A_73]: (r2_hidden('#skF_3'(A_73), k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski(A_73, '#skF_5') | k1_xboole_0=A_73)), inference(resolution, [status(thm)], [c_70, c_242])).
% 2.38/1.29  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.38/1.29  tff(c_141, plain, (![A_52, B_53]: (k4_xboole_0(A_52, B_53)=k3_subset_1(A_52, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.38/1.29  tff(c_145, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_141])).
% 2.38/1.29  tff(c_26, plain, (![A_18, C_20, B_19]: (r1_xboole_0(A_18, k4_xboole_0(C_20, B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.38/1.29  tff(c_120, plain, (![A_44, B_45, C_46]: (~r1_xboole_0(A_44, B_45) | ~r2_hidden(C_46, B_45) | ~r2_hidden(C_46, A_44))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.38/1.29  tff(c_170, plain, (![C_61, C_62, B_63, A_64]: (~r2_hidden(C_61, k4_xboole_0(C_62, B_63)) | ~r2_hidden(C_61, A_64) | ~r1_tarski(A_64, B_63))), inference(resolution, [status(thm)], [c_26, c_120])).
% 2.38/1.29  tff(c_178, plain, (![C_61, A_64]: (~r2_hidden(C_61, k3_subset_1('#skF_4', '#skF_5')) | ~r2_hidden(C_61, A_64) | ~r1_tarski(A_64, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_170])).
% 2.38/1.29  tff(c_259, plain, (![A_74, A_75]: (~r2_hidden('#skF_3'(A_74), A_75) | ~r1_tarski(A_75, '#skF_5') | ~r1_tarski(A_74, '#skF_5') | k1_xboole_0=A_74)), inference(resolution, [status(thm)], [c_252, c_178])).
% 2.38/1.29  tff(c_272, plain, (![A_76]: (~r1_tarski(A_76, '#skF_5') | k1_xboole_0=A_76)), inference(resolution, [status(thm)], [c_14, c_259])).
% 2.38/1.29  tff(c_280, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_20, c_272])).
% 2.38/1.29  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_280])).
% 2.38/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.29  
% 2.38/1.29  Inference rules
% 2.38/1.29  ----------------------
% 2.38/1.29  #Ref     : 0
% 2.38/1.29  #Sup     : 54
% 2.38/1.29  #Fact    : 0
% 2.38/1.29  #Define  : 0
% 2.38/1.29  #Split   : 3
% 2.38/1.29  #Chain   : 0
% 2.38/1.29  #Close   : 0
% 2.38/1.29  
% 2.38/1.29  Ordering : KBO
% 2.38/1.29  
% 2.38/1.29  Simplification rules
% 2.38/1.29  ----------------------
% 2.38/1.29  #Subsume      : 7
% 2.38/1.29  #Demod        : 10
% 2.38/1.29  #Tautology    : 18
% 2.38/1.29  #SimpNegUnit  : 3
% 2.38/1.29  #BackRed      : 4
% 2.38/1.29  
% 2.38/1.29  #Partial instantiations: 0
% 2.38/1.29  #Strategies tried      : 1
% 2.38/1.29  
% 2.38/1.29  Timing (in seconds)
% 2.38/1.29  ----------------------
% 2.38/1.29  Preprocessing        : 0.31
% 2.38/1.29  Parsing              : 0.16
% 2.38/1.30  CNF conversion       : 0.02
% 2.38/1.30  Main loop            : 0.22
% 2.38/1.30  Inferencing          : 0.07
% 2.38/1.30  Reduction            : 0.06
% 2.38/1.30  Demodulation         : 0.04
% 2.38/1.30  BG Simplification    : 0.01
% 2.38/1.30  Subsumption          : 0.05
% 2.38/1.30  Abstraction          : 0.01
% 2.38/1.30  MUC search           : 0.00
% 2.38/1.30  Cooper               : 0.00
% 2.38/1.30  Total                : 0.56
% 2.38/1.30  Index Insertion      : 0.00
% 2.38/1.30  Index Deletion       : 0.00
% 2.38/1.30  Index Matching       : 0.00
% 2.38/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
