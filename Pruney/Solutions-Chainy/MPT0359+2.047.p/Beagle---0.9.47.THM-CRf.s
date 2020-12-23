%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:15 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 118 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 167 expanded)
%              Number of equality atoms :   25 (  73 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_53,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(c_18,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_30])).

tff(c_81,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_36,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_39,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_36])).

tff(c_82,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_39])).

tff(c_83,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_81])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_84,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_28])).

tff(c_159,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = k3_subset_1(A_39,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_166,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_subset_1('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_159])).

tff(c_12,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_201,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_12])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_201])).

tff(c_206,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_207,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_268,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = k3_subset_1(A_48,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_277,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_268])).

tff(c_320,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_tarski(A_51,k2_xboole_0(B_52,C_53))
      | ~ r1_tarski(k4_xboole_0(A_51,B_52),C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_377,plain,(
    ! [C_58] :
      ( r1_tarski('#skF_1',k2_xboole_0('#skF_2',C_58))
      | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),C_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_320])).

tff(c_391,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_207,c_377])).

tff(c_401,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_391])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_405,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_401,c_4])).

tff(c_408,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_405])).

tff(c_16,plain,(
    ! [A_11] : k1_subset_1(A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_15] : m1_subset_1(k1_subset_1(A_15),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_41,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22])).

tff(c_24,plain,(
    ! [A_16] : k3_subset_1(A_16,k1_subset_1(A_16)) = k2_subset_1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_37,plain,(
    ! [A_16] : k3_subset_1(A_16,k1_subset_1(A_16)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_24])).

tff(c_40,plain,(
    ! [A_16] : k3_subset_1(A_16,k1_xboole_0) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_37])).

tff(c_10,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_428,plain,(
    ! [C_61,A_62,B_63] :
      ( r1_tarski(C_61,k3_subset_1(A_62,B_63))
      | ~ r1_tarski(B_63,k3_subset_1(A_62,C_61))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_62))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_439,plain,(
    ! [C_61,A_62] :
      ( r1_tarski(C_61,k3_subset_1(A_62,k1_xboole_0))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_62))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_62)) ) ),
    inference(resolution,[status(thm)],[c_10,c_428])).

tff(c_447,plain,(
    ! [C_64,A_65] :
      ( r1_tarski(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_65)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_40,c_439])).

tff(c_453,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_447])).

tff(c_459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_408,c_453])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.36  
% 2.25/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.36  %$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.25/1.36  
% 2.25/1.36  %Foreground sorts:
% 2.25/1.36  
% 2.25/1.36  
% 2.25/1.36  %Background operators:
% 2.25/1.36  
% 2.25/1.36  
% 2.25/1.36  %Foreground operators:
% 2.25/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.25/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.25/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.36  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.25/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.25/1.36  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.25/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.36  
% 2.25/1.37  tff(f_45, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.25/1.37  tff(f_69, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 2.25/1.37  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.25/1.37  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.25/1.37  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.25/1.37  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.25/1.37  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.25/1.37  tff(f_43, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.25/1.37  tff(f_51, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 2.25/1.37  tff(f_53, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.25/1.37  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.25/1.37  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 2.25/1.37  tff(c_18, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.25/1.37  tff(c_30, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.25/1.37  tff(c_38, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_30])).
% 2.25/1.37  tff(c_81, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_38])).
% 2.25/1.37  tff(c_36, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.25/1.37  tff(c_39, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_36])).
% 2.25/1.37  tff(c_82, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_81, c_39])).
% 2.25/1.37  tff(c_83, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_81])).
% 2.25/1.37  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.25/1.37  tff(c_84, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_28])).
% 2.25/1.37  tff(c_159, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=k3_subset_1(A_39, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.25/1.37  tff(c_166, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_subset_1('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_159])).
% 2.25/1.37  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.25/1.37  tff(c_201, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_166, c_12])).
% 2.25/1.37  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_201])).
% 2.25/1.37  tff(c_206, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_38])).
% 2.25/1.37  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.25/1.37  tff(c_207, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 2.25/1.37  tff(c_268, plain, (![A_48, B_49]: (k4_xboole_0(A_48, B_49)=k3_subset_1(A_48, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.25/1.37  tff(c_277, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_268])).
% 2.25/1.37  tff(c_320, plain, (![A_51, B_52, C_53]: (r1_tarski(A_51, k2_xboole_0(B_52, C_53)) | ~r1_tarski(k4_xboole_0(A_51, B_52), C_53))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.25/1.37  tff(c_377, plain, (![C_58]: (r1_tarski('#skF_1', k2_xboole_0('#skF_2', C_58)) | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), C_58))), inference(superposition, [status(thm), theory('equality')], [c_277, c_320])).
% 2.25/1.37  tff(c_391, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_207, c_377])).
% 2.25/1.37  tff(c_401, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_391])).
% 2.25/1.37  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.25/1.37  tff(c_405, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_401, c_4])).
% 2.25/1.37  tff(c_408, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_206, c_405])).
% 2.25/1.37  tff(c_16, plain, (![A_11]: (k1_subset_1(A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.25/1.37  tff(c_22, plain, (![A_15]: (m1_subset_1(k1_subset_1(A_15), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.25/1.37  tff(c_41, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22])).
% 2.25/1.37  tff(c_24, plain, (![A_16]: (k3_subset_1(A_16, k1_subset_1(A_16))=k2_subset_1(A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.25/1.37  tff(c_37, plain, (![A_16]: (k3_subset_1(A_16, k1_subset_1(A_16))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_24])).
% 2.25/1.37  tff(c_40, plain, (![A_16]: (k3_subset_1(A_16, k1_xboole_0)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_37])).
% 2.25/1.37  tff(c_10, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.25/1.37  tff(c_428, plain, (![C_61, A_62, B_63]: (r1_tarski(C_61, k3_subset_1(A_62, B_63)) | ~r1_tarski(B_63, k3_subset_1(A_62, C_61)) | ~m1_subset_1(C_61, k1_zfmisc_1(A_62)) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.25/1.37  tff(c_439, plain, (![C_61, A_62]: (r1_tarski(C_61, k3_subset_1(A_62, k1_xboole_0)) | ~m1_subset_1(C_61, k1_zfmisc_1(A_62)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_62)))), inference(resolution, [status(thm)], [c_10, c_428])).
% 2.25/1.37  tff(c_447, plain, (![C_64, A_65]: (r1_tarski(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(A_65)))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_40, c_439])).
% 2.25/1.37  tff(c_453, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_447])).
% 2.25/1.37  tff(c_459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_408, c_453])).
% 2.25/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.37  
% 2.25/1.37  Inference rules
% 2.25/1.37  ----------------------
% 2.25/1.37  #Ref     : 0
% 2.25/1.37  #Sup     : 92
% 2.25/1.37  #Fact    : 0
% 2.25/1.37  #Define  : 0
% 2.25/1.37  #Split   : 3
% 2.25/1.38  #Chain   : 0
% 2.25/1.38  #Close   : 0
% 2.25/1.38  
% 2.25/1.38  Ordering : KBO
% 2.25/1.38  
% 2.25/1.38  Simplification rules
% 2.25/1.38  ----------------------
% 2.25/1.38  #Subsume      : 0
% 2.25/1.38  #Demod        : 40
% 2.25/1.38  #Tautology    : 53
% 2.25/1.38  #SimpNegUnit  : 5
% 2.25/1.38  #BackRed      : 2
% 2.25/1.38  
% 2.25/1.38  #Partial instantiations: 0
% 2.25/1.38  #Strategies tried      : 1
% 2.25/1.38  
% 2.25/1.38  Timing (in seconds)
% 2.25/1.38  ----------------------
% 2.44/1.38  Preprocessing        : 0.30
% 2.44/1.38  Parsing              : 0.17
% 2.44/1.38  CNF conversion       : 0.02
% 2.44/1.38  Main loop            : 0.22
% 2.44/1.38  Inferencing          : 0.08
% 2.44/1.38  Reduction            : 0.07
% 2.44/1.38  Demodulation         : 0.06
% 2.44/1.38  BG Simplification    : 0.01
% 2.44/1.38  Subsumption          : 0.04
% 2.44/1.38  Abstraction          : 0.01
% 2.44/1.38  MUC search           : 0.00
% 2.44/1.38  Cooper               : 0.00
% 2.44/1.38  Total                : 0.56
% 2.44/1.38  Index Insertion      : 0.00
% 2.44/1.38  Index Deletion       : 0.00
% 2.44/1.38  Index Matching       : 0.00
% 2.44/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
