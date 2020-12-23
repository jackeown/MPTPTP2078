%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:16 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   68 (  83 expanded)
%              Number of leaves         :   35 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 121 expanded)
%              Number of equality atoms :   28 (  41 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_50,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_60,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_9'))
    | k11_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_98,plain,(
    k11_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_251,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_1'(A_91,B_92),B_92)
      | r2_hidden('#skF_2'(A_91,B_92),A_91)
      | B_92 = A_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_100,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,k3_xboole_0(A_54,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_103,plain,(
    ! [A_9,C_56] :
      ( ~ r1_xboole_0(A_9,k1_xboole_0)
      | ~ r2_hidden(C_56,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_100])).

tff(c_105,plain,(
    ! [C_56] : ~ r2_hidden(C_56,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_103])).

tff(c_294,plain,(
    ! [B_93] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_93),B_93)
      | k1_xboole_0 = B_93 ) ),
    inference(resolution,[status(thm)],[c_251,c_105])).

tff(c_201,plain,(
    ! [A_80,B_81,C_82] :
      ( r2_hidden(k4_tarski(A_80,B_81),C_82)
      | ~ r2_hidden(B_81,k11_relat_1(C_82,A_80))
      | ~ v1_relat_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    ! [C_35,A_20,D_38] :
      ( r2_hidden(C_35,k1_relat_1(A_20))
      | ~ r2_hidden(k4_tarski(C_35,D_38),A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_222,plain,(
    ! [A_80,C_82,B_81] :
      ( r2_hidden(A_80,k1_relat_1(C_82))
      | ~ r2_hidden(B_81,k11_relat_1(C_82,A_80))
      | ~ v1_relat_1(C_82) ) ),
    inference(resolution,[status(thm)],[c_201,c_34])).

tff(c_694,plain,(
    ! [A_120,C_121] :
      ( r2_hidden(A_120,k1_relat_1(C_121))
      | ~ v1_relat_1(C_121)
      | k11_relat_1(C_121,A_120) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_294,c_222])).

tff(c_54,plain,
    ( k11_relat_1('#skF_9','#skF_8') = k1_xboole_0
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_99,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_723,plain,
    ( ~ v1_relat_1('#skF_9')
    | k11_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_694,c_99])).

tff(c_742,plain,(
    k11_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_723])).

tff(c_744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_742])).

tff(c_745,plain,(
    k11_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_745])).

tff(c_749,plain,(
    k11_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_30,plain,(
    ! [A_17,B_19] :
      ( k9_relat_1(A_17,k1_tarski(B_19)) = k11_relat_1(A_17,B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_748,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_794,plain,(
    ! [B_137,A_138] :
      ( r1_xboole_0(k1_relat_1(B_137),A_138)
      | k9_relat_1(B_137,A_138) != k1_xboole_0
      | ~ v1_relat_1(B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1071,plain,(
    ! [B_174,A_175] :
      ( k4_xboole_0(k1_relat_1(B_174),A_175) = k1_relat_1(B_174)
      | k9_relat_1(B_174,A_175) != k1_xboole_0
      | ~ v1_relat_1(B_174) ) ),
    inference(resolution,[status(thm)],[c_794,c_18])).

tff(c_26,plain,(
    ! [C_16,B_15] : ~ r2_hidden(C_16,k4_xboole_0(B_15,k1_tarski(C_16))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1543,plain,(
    ! [C_199,B_200] :
      ( ~ r2_hidden(C_199,k1_relat_1(B_200))
      | k9_relat_1(B_200,k1_tarski(C_199)) != k1_xboole_0
      | ~ v1_relat_1(B_200) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1071,c_26])).

tff(c_1598,plain,
    ( k9_relat_1('#skF_9',k1_tarski('#skF_8')) != k1_xboole_0
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_748,c_1543])).

tff(c_1612,plain,(
    k9_relat_1('#skF_9',k1_tarski('#skF_8')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1598])).

tff(c_1615,plain,
    ( k11_relat_1('#skF_9','#skF_8') != k1_xboole_0
    | ~ v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1612])).

tff(c_1618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_749,c_1615])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:06:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.54  
% 3.03/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.54  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 3.03/1.54  
% 3.03/1.54  %Foreground sorts:
% 3.03/1.54  
% 3.03/1.54  
% 3.03/1.54  %Background operators:
% 3.03/1.54  
% 3.03/1.54  
% 3.03/1.54  %Foreground operators:
% 3.03/1.54  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.03/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.03/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.03/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.03/1.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.03/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.03/1.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.03/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.03/1.54  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.03/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.03/1.54  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.03/1.54  tff('#skF_9', type, '#skF_9': $i).
% 3.03/1.54  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.03/1.54  tff('#skF_8', type, '#skF_8': $i).
% 3.03/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.03/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.03/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.03/1.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.03/1.54  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.03/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.03/1.54  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.03/1.54  
% 3.27/1.55  tff(f_96, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.27/1.55  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.27/1.55  tff(f_50, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.27/1.55  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.27/1.55  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.27/1.55  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 3.27/1.55  tff(f_76, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.27/1.55  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 3.27/1.55  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 3.27/1.55  tff(f_54, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.27/1.55  tff(f_63, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.27/1.55  tff(c_52, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.27/1.55  tff(c_60, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_9')) | k11_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.27/1.55  tff(c_98, plain, (k11_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 3.27/1.55  tff(c_251, plain, (![A_91, B_92]: (r2_hidden('#skF_1'(A_91, B_92), B_92) | r2_hidden('#skF_2'(A_91, B_92), A_91) | B_92=A_91)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.27/1.55  tff(c_16, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.27/1.55  tff(c_14, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.27/1.55  tff(c_100, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, k3_xboole_0(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.27/1.55  tff(c_103, plain, (![A_9, C_56]: (~r1_xboole_0(A_9, k1_xboole_0) | ~r2_hidden(C_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_100])).
% 3.27/1.55  tff(c_105, plain, (![C_56]: (~r2_hidden(C_56, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_103])).
% 3.27/1.55  tff(c_294, plain, (![B_93]: (r2_hidden('#skF_1'(k1_xboole_0, B_93), B_93) | k1_xboole_0=B_93)), inference(resolution, [status(thm)], [c_251, c_105])).
% 3.27/1.55  tff(c_201, plain, (![A_80, B_81, C_82]: (r2_hidden(k4_tarski(A_80, B_81), C_82) | ~r2_hidden(B_81, k11_relat_1(C_82, A_80)) | ~v1_relat_1(C_82))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.27/1.55  tff(c_34, plain, (![C_35, A_20, D_38]: (r2_hidden(C_35, k1_relat_1(A_20)) | ~r2_hidden(k4_tarski(C_35, D_38), A_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.27/1.55  tff(c_222, plain, (![A_80, C_82, B_81]: (r2_hidden(A_80, k1_relat_1(C_82)) | ~r2_hidden(B_81, k11_relat_1(C_82, A_80)) | ~v1_relat_1(C_82))), inference(resolution, [status(thm)], [c_201, c_34])).
% 3.27/1.55  tff(c_694, plain, (![A_120, C_121]: (r2_hidden(A_120, k1_relat_1(C_121)) | ~v1_relat_1(C_121) | k11_relat_1(C_121, A_120)=k1_xboole_0)), inference(resolution, [status(thm)], [c_294, c_222])).
% 3.27/1.55  tff(c_54, plain, (k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0 | ~r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.27/1.55  tff(c_99, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_54])).
% 3.27/1.55  tff(c_723, plain, (~v1_relat_1('#skF_9') | k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_694, c_99])).
% 3.27/1.55  tff(c_742, plain, (k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_723])).
% 3.27/1.55  tff(c_744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_742])).
% 3.27/1.55  tff(c_745, plain, (k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 3.27/1.55  tff(c_747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_745])).
% 3.27/1.55  tff(c_749, plain, (k11_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 3.27/1.55  tff(c_30, plain, (![A_17, B_19]: (k9_relat_1(A_17, k1_tarski(B_19))=k11_relat_1(A_17, B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.27/1.55  tff(c_748, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_60])).
% 3.27/1.55  tff(c_794, plain, (![B_137, A_138]: (r1_xboole_0(k1_relat_1(B_137), A_138) | k9_relat_1(B_137, A_138)!=k1_xboole_0 | ~v1_relat_1(B_137))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.27/1.55  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.27/1.55  tff(c_1071, plain, (![B_174, A_175]: (k4_xboole_0(k1_relat_1(B_174), A_175)=k1_relat_1(B_174) | k9_relat_1(B_174, A_175)!=k1_xboole_0 | ~v1_relat_1(B_174))), inference(resolution, [status(thm)], [c_794, c_18])).
% 3.27/1.55  tff(c_26, plain, (![C_16, B_15]: (~r2_hidden(C_16, k4_xboole_0(B_15, k1_tarski(C_16))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.27/1.55  tff(c_1543, plain, (![C_199, B_200]: (~r2_hidden(C_199, k1_relat_1(B_200)) | k9_relat_1(B_200, k1_tarski(C_199))!=k1_xboole_0 | ~v1_relat_1(B_200))), inference(superposition, [status(thm), theory('equality')], [c_1071, c_26])).
% 3.27/1.55  tff(c_1598, plain, (k9_relat_1('#skF_9', k1_tarski('#skF_8'))!=k1_xboole_0 | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_748, c_1543])).
% 3.27/1.55  tff(c_1612, plain, (k9_relat_1('#skF_9', k1_tarski('#skF_8'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1598])).
% 3.27/1.55  tff(c_1615, plain, (k11_relat_1('#skF_9', '#skF_8')!=k1_xboole_0 | ~v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_30, c_1612])).
% 3.27/1.55  tff(c_1618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_749, c_1615])).
% 3.27/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.55  
% 3.27/1.55  Inference rules
% 3.27/1.55  ----------------------
% 3.27/1.55  #Ref     : 0
% 3.27/1.55  #Sup     : 327
% 3.27/1.55  #Fact    : 0
% 3.27/1.55  #Define  : 0
% 3.27/1.55  #Split   : 4
% 3.27/1.55  #Chain   : 0
% 3.27/1.55  #Close   : 0
% 3.27/1.55  
% 3.27/1.55  Ordering : KBO
% 3.27/1.55  
% 3.27/1.55  Simplification rules
% 3.27/1.55  ----------------------
% 3.27/1.55  #Subsume      : 82
% 3.27/1.55  #Demod        : 70
% 3.27/1.55  #Tautology    : 81
% 3.27/1.55  #SimpNegUnit  : 12
% 3.27/1.55  #BackRed      : 2
% 3.27/1.55  
% 3.27/1.55  #Partial instantiations: 0
% 3.27/1.55  #Strategies tried      : 1
% 3.27/1.55  
% 3.27/1.55  Timing (in seconds)
% 3.27/1.55  ----------------------
% 3.27/1.55  Preprocessing        : 0.30
% 3.27/1.56  Parsing              : 0.15
% 3.27/1.56  CNF conversion       : 0.02
% 3.27/1.56  Main loop            : 0.43
% 3.27/1.56  Inferencing          : 0.17
% 3.27/1.56  Reduction            : 0.12
% 3.27/1.56  Demodulation         : 0.08
% 3.27/1.56  BG Simplification    : 0.02
% 3.27/1.56  Subsumption          : 0.08
% 3.27/1.56  Abstraction          : 0.03
% 3.27/1.56  MUC search           : 0.00
% 3.27/1.56  Cooper               : 0.00
% 3.27/1.56  Total                : 0.76
% 3.27/1.56  Index Insertion      : 0.00
% 3.27/1.56  Index Deletion       : 0.00
% 3.27/1.56  Index Matching       : 0.00
% 3.27/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
