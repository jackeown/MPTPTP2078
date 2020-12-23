%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:06 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   61 (  87 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 125 expanded)
%              Number of equality atoms :   24 (  43 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_62,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_113,plain,(
    ! [A_49,B_50] :
      ( ~ r2_hidden('#skF_2'(A_49,B_50),B_50)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_119,plain,(
    ! [A_51] : r1_tarski(A_51,A_51) ),
    inference(resolution,[status(thm)],[c_10,c_113])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_123,plain,(
    ! [A_51] : k3_xboole_0(A_51,A_51) = A_51 ),
    inference(resolution,[status(thm)],[c_119,c_18])).

tff(c_118,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_113])).

tff(c_24,plain,(
    ! [A_20] : k1_subset_1(A_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_37,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_52,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_37])).

tff(c_36,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_36])).

tff(c_54,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_38])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k3_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k3_xboole_0(A_10,B_11) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_14])).

tff(c_97,plain,(
    ! [B_42,A_43] :
      ( ~ r1_xboole_0(B_42,A_43)
      | ~ r1_tarski(B_42,A_43)
      | v1_xboole_0(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_181,plain,(
    ! [A_63,B_64] :
      ( ~ r1_tarski(A_63,B_64)
      | v1_xboole_0(A_63)
      | k3_xboole_0(A_63,B_64) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_68,c_97])).

tff(c_184,plain,(
    ! [A_5] :
      ( v1_xboole_0(A_5)
      | k3_xboole_0(A_5,A_5) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_118,c_181])).

tff(c_191,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_184])).

tff(c_78,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_2'(A_38,B_39),A_38)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [A_40,B_41] :
      ( ~ v1_xboole_0(A_40)
      | r1_tarski(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_78,c_2])).

tff(c_96,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_83,c_52])).

tff(c_194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_96])).

tff(c_195,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_196,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_375,plain,(
    ! [A_99,B_100] :
      ( k4_xboole_0(A_99,B_100) = k3_subset_1(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_379,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_375])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k4_xboole_0(B_17,A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_383,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_20])).

tff(c_387,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_383])).

tff(c_389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_387])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.41  
% 2.16/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.16/1.41  
% 2.16/1.41  %Foreground sorts:
% 2.16/1.41  
% 2.16/1.41  
% 2.16/1.41  %Background operators:
% 2.16/1.41  
% 2.16/1.41  
% 2.16/1.41  %Foreground operators:
% 2.16/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.16/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.16/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.16/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.16/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.41  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.16/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.41  
% 2.16/1.42  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.16/1.42  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.16/1.42  tff(f_62, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.16/1.42  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.16/1.42  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.16/1.42  tff(f_60, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.16/1.42  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.16/1.42  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.16/1.42  tff(f_52, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.16/1.42  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.16/1.42  tff(c_113, plain, (![A_49, B_50]: (~r2_hidden('#skF_2'(A_49, B_50), B_50) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.16/1.42  tff(c_119, plain, (![A_51]: (r1_tarski(A_51, A_51))), inference(resolution, [status(thm)], [c_10, c_113])).
% 2.16/1.42  tff(c_18, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.16/1.42  tff(c_123, plain, (![A_51]: (k3_xboole_0(A_51, A_51)=A_51)), inference(resolution, [status(thm)], [c_119, c_18])).
% 2.16/1.42  tff(c_118, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_113])).
% 2.16/1.42  tff(c_24, plain, (![A_20]: (k1_subset_1(A_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.16/1.42  tff(c_30, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.16/1.42  tff(c_37, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_30])).
% 2.16/1.42  tff(c_52, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_37])).
% 2.16/1.42  tff(c_36, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.16/1.42  tff(c_38, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_36])).
% 2.16/1.42  tff(c_54, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_38])).
% 2.16/1.42  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k3_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.16/1.42  tff(c_68, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k3_xboole_0(A_10, B_11)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_14])).
% 2.16/1.42  tff(c_97, plain, (![B_42, A_43]: (~r1_xboole_0(B_42, A_43) | ~r1_tarski(B_42, A_43) | v1_xboole_0(B_42))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.16/1.42  tff(c_181, plain, (![A_63, B_64]: (~r1_tarski(A_63, B_64) | v1_xboole_0(A_63) | k3_xboole_0(A_63, B_64)!='#skF_4')), inference(resolution, [status(thm)], [c_68, c_97])).
% 2.16/1.42  tff(c_184, plain, (![A_5]: (v1_xboole_0(A_5) | k3_xboole_0(A_5, A_5)!='#skF_4')), inference(resolution, [status(thm)], [c_118, c_181])).
% 2.16/1.42  tff(c_191, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_184])).
% 2.16/1.42  tff(c_78, plain, (![A_38, B_39]: (r2_hidden('#skF_2'(A_38, B_39), A_38) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.16/1.42  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.42  tff(c_83, plain, (![A_40, B_41]: (~v1_xboole_0(A_40) | r1_tarski(A_40, B_41))), inference(resolution, [status(thm)], [c_78, c_2])).
% 2.16/1.42  tff(c_96, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_83, c_52])).
% 2.16/1.42  tff(c_194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_191, c_96])).
% 2.16/1.42  tff(c_195, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_37])).
% 2.16/1.42  tff(c_196, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_37])).
% 2.16/1.42  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.16/1.42  tff(c_375, plain, (![A_99, B_100]: (k4_xboole_0(A_99, B_100)=k3_subset_1(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.16/1.42  tff(c_379, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_375])).
% 2.16/1.42  tff(c_20, plain, (![A_16, B_17]: (k1_xboole_0=A_16 | ~r1_tarski(A_16, k4_xboole_0(B_17, A_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.16/1.42  tff(c_383, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_379, c_20])).
% 2.16/1.42  tff(c_387, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_383])).
% 2.16/1.42  tff(c_389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195, c_387])).
% 2.16/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.42  
% 2.16/1.42  Inference rules
% 2.16/1.42  ----------------------
% 2.16/1.42  #Ref     : 0
% 2.16/1.42  #Sup     : 81
% 2.16/1.42  #Fact    : 0
% 2.16/1.42  #Define  : 0
% 2.16/1.42  #Split   : 1
% 2.16/1.42  #Chain   : 0
% 2.16/1.42  #Close   : 0
% 2.16/1.42  
% 2.16/1.42  Ordering : KBO
% 2.16/1.42  
% 2.16/1.42  Simplification rules
% 2.16/1.42  ----------------------
% 2.16/1.42  #Subsume      : 8
% 2.16/1.42  #Demod        : 14
% 2.16/1.42  #Tautology    : 41
% 2.16/1.42  #SimpNegUnit  : 3
% 2.16/1.42  #BackRed      : 3
% 2.16/1.42  
% 2.16/1.42  #Partial instantiations: 0
% 2.16/1.43  #Strategies tried      : 1
% 2.16/1.43  
% 2.16/1.43  Timing (in seconds)
% 2.16/1.43  ----------------------
% 2.16/1.43  Preprocessing        : 0.31
% 2.16/1.43  Parsing              : 0.16
% 2.16/1.43  CNF conversion       : 0.02
% 2.16/1.43  Main loop            : 0.22
% 2.16/1.43  Inferencing          : 0.09
% 2.16/1.43  Reduction            : 0.06
% 2.16/1.43  Demodulation         : 0.04
% 2.16/1.43  BG Simplification    : 0.01
% 2.16/1.43  Subsumption          : 0.03
% 2.16/1.43  Abstraction          : 0.01
% 2.16/1.43  MUC search           : 0.00
% 2.16/1.43  Cooper               : 0.00
% 2.16/1.43  Total                : 0.56
% 2.16/1.43  Index Insertion      : 0.00
% 2.16/1.43  Index Deletion       : 0.00
% 2.16/1.43  Index Matching       : 0.00
% 2.16/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
