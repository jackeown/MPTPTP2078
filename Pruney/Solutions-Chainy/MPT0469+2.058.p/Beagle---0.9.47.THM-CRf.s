%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:59 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   58 (  84 expanded)
%              Number of leaves         :   32 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 ( 104 expanded)
%              Number of equality atoms :   21 (  34 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k3_tarski > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_6 > #skF_3 > #skF_12 > #skF_5 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_54,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_67,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_28,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_207,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_3'(A_100,B_101),A_100)
      | r2_hidden('#skF_4'(A_100,B_101),B_101)
      | k3_tarski(A_100) = B_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_68,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,k3_xboole_0(A_67,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_71,plain,(
    ! [A_6,C_69] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_69,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_68])).

tff(c_73,plain,(
    ! [C_69] : ~ r2_hidden(C_69,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_71])).

tff(c_229,plain,(
    ! [B_101] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_101),B_101)
      | k3_tarski(k1_xboole_0) = B_101 ) ),
    inference(resolution,[status(thm)],[c_207,c_73])).

tff(c_497,plain,(
    ! [B_113] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_113),B_113)
      | k1_xboole_0 = B_113 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_229])).

tff(c_272,plain,(
    ! [C_102,A_103] :
      ( r2_hidden(k4_tarski(C_102,'#skF_9'(A_103,k1_relat_1(A_103),C_102)),A_103)
      | ~ r2_hidden(C_102,k1_relat_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_312,plain,(
    ! [C_102] : ~ r2_hidden(C_102,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_272,c_73])).

tff(c_525,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_497,c_312])).

tff(c_561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_525])).

tff(c_562,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_673,plain,(
    ! [A_145,B_146] :
      ( r2_hidden('#skF_3'(A_145,B_146),A_145)
      | r2_hidden('#skF_4'(A_145,B_146),B_146)
      | k3_tarski(A_145) = B_146 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_568,plain,(
    ! [A_114,B_115,C_116] :
      ( ~ r1_xboole_0(A_114,B_115)
      | ~ r2_hidden(C_116,k3_xboole_0(A_114,B_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_571,plain,(
    ! [A_6,C_116] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_116,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_568])).

tff(c_573,plain,(
    ! [C_116] : ~ r2_hidden(C_116,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_571])).

tff(c_695,plain,(
    ! [B_146] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_146),B_146)
      | k3_tarski(k1_xboole_0) = B_146 ) ),
    inference(resolution,[status(thm)],[c_673,c_573])).

tff(c_730,plain,(
    ! [B_146] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_146),B_146)
      | k1_xboole_0 = B_146 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_695])).

tff(c_773,plain,(
    ! [A_148,C_149] :
      ( r2_hidden(k4_tarski('#skF_13'(A_148,k2_relat_1(A_148),C_149),C_149),A_148)
      | ~ r2_hidden(C_149,k2_relat_1(A_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_815,plain,(
    ! [C_150] : ~ r2_hidden(C_150,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_773,c_573])).

tff(c_823,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_730,c_815])).

tff(c_840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_562,c_823])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.35  
% 2.22/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.35  %$ r2_hidden > r1_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k3_tarski > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_13 > #skF_11 > #skF_6 > #skF_3 > #skF_12 > #skF_5 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_4
% 2.22/1.35  
% 2.22/1.35  %Foreground sorts:
% 2.22/1.35  
% 2.22/1.35  
% 2.22/1.35  %Background operators:
% 2.22/1.35  
% 2.22/1.35  
% 2.22/1.35  %Foreground operators:
% 2.22/1.35  tff('#skF_13', type, '#skF_13': ($i * $i * $i) > $i).
% 2.22/1.35  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 2.22/1.35  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.22/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.22/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.22/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.35  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 2.22/1.35  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.22/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.22/1.35  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 2.22/1.35  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.22/1.35  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 2.22/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.22/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.22/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.35  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.22/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.22/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.22/1.35  
% 2.22/1.36  tff(f_74, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.22/1.36  tff(f_54, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.22/1.36  tff(f_53, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.22/1.36  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.22/1.36  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.22/1.36  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.22/1.36  tff(f_62, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.22/1.36  tff(f_70, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.22/1.36  tff(c_54, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.22/1.36  tff(c_67, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 2.22/1.36  tff(c_28, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.22/1.36  tff(c_207, plain, (![A_100, B_101]: (r2_hidden('#skF_3'(A_100, B_101), A_100) | r2_hidden('#skF_4'(A_100, B_101), B_101) | k3_tarski(A_100)=B_101)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.22/1.36  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.36  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.22/1.36  tff(c_68, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, k3_xboole_0(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.36  tff(c_71, plain, (![A_6, C_69]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_69, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_68])).
% 2.22/1.36  tff(c_73, plain, (![C_69]: (~r2_hidden(C_69, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_71])).
% 2.22/1.36  tff(c_229, plain, (![B_101]: (r2_hidden('#skF_4'(k1_xboole_0, B_101), B_101) | k3_tarski(k1_xboole_0)=B_101)), inference(resolution, [status(thm)], [c_207, c_73])).
% 2.22/1.36  tff(c_497, plain, (![B_113]: (r2_hidden('#skF_4'(k1_xboole_0, B_113), B_113) | k1_xboole_0=B_113)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_229])).
% 2.22/1.36  tff(c_272, plain, (![C_102, A_103]: (r2_hidden(k4_tarski(C_102, '#skF_9'(A_103, k1_relat_1(A_103), C_102)), A_103) | ~r2_hidden(C_102, k1_relat_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.22/1.36  tff(c_312, plain, (![C_102]: (~r2_hidden(C_102, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_272, c_73])).
% 2.22/1.36  tff(c_525, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_497, c_312])).
% 2.22/1.36  tff(c_561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_525])).
% 2.22/1.36  tff(c_562, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 2.22/1.36  tff(c_673, plain, (![A_145, B_146]: (r2_hidden('#skF_3'(A_145, B_146), A_145) | r2_hidden('#skF_4'(A_145, B_146), B_146) | k3_tarski(A_145)=B_146)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.22/1.36  tff(c_568, plain, (![A_114, B_115, C_116]: (~r1_xboole_0(A_114, B_115) | ~r2_hidden(C_116, k3_xboole_0(A_114, B_115)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.36  tff(c_571, plain, (![A_6, C_116]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_116, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_568])).
% 2.22/1.36  tff(c_573, plain, (![C_116]: (~r2_hidden(C_116, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_571])).
% 2.22/1.36  tff(c_695, plain, (![B_146]: (r2_hidden('#skF_4'(k1_xboole_0, B_146), B_146) | k3_tarski(k1_xboole_0)=B_146)), inference(resolution, [status(thm)], [c_673, c_573])).
% 2.22/1.36  tff(c_730, plain, (![B_146]: (r2_hidden('#skF_4'(k1_xboole_0, B_146), B_146) | k1_xboole_0=B_146)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_695])).
% 2.22/1.36  tff(c_773, plain, (![A_148, C_149]: (r2_hidden(k4_tarski('#skF_13'(A_148, k2_relat_1(A_148), C_149), C_149), A_148) | ~r2_hidden(C_149, k2_relat_1(A_148)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.22/1.36  tff(c_815, plain, (![C_150]: (~r2_hidden(C_150, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_773, c_573])).
% 2.22/1.36  tff(c_823, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_730, c_815])).
% 2.22/1.36  tff(c_840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_562, c_823])).
% 2.22/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.36  
% 2.22/1.36  Inference rules
% 2.22/1.36  ----------------------
% 2.22/1.36  #Ref     : 0
% 2.22/1.36  #Sup     : 158
% 2.22/1.36  #Fact    : 0
% 2.22/1.36  #Define  : 0
% 2.22/1.36  #Split   : 1
% 2.22/1.36  #Chain   : 0
% 2.22/1.36  #Close   : 0
% 2.22/1.36  
% 2.22/1.36  Ordering : KBO
% 2.22/1.36  
% 2.22/1.36  Simplification rules
% 2.22/1.36  ----------------------
% 2.22/1.36  #Subsume      : 27
% 2.22/1.36  #Demod        : 40
% 2.22/1.36  #Tautology    : 13
% 2.22/1.36  #SimpNegUnit  : 6
% 2.22/1.36  #BackRed      : 0
% 2.22/1.36  
% 2.22/1.36  #Partial instantiations: 0
% 2.22/1.36  #Strategies tried      : 1
% 2.22/1.36  
% 2.22/1.36  Timing (in seconds)
% 2.22/1.36  ----------------------
% 2.22/1.37  Preprocessing        : 0.29
% 2.22/1.37  Parsing              : 0.15
% 2.22/1.37  CNF conversion       : 0.03
% 2.22/1.37  Main loop            : 0.30
% 2.22/1.37  Inferencing          : 0.11
% 2.22/1.37  Reduction            : 0.08
% 2.22/1.37  Demodulation         : 0.05
% 2.22/1.37  BG Simplification    : 0.02
% 2.22/1.37  Subsumption          : 0.06
% 2.22/1.37  Abstraction          : 0.02
% 2.22/1.37  MUC search           : 0.00
% 2.22/1.37  Cooper               : 0.00
% 2.22/1.37  Total                : 0.62
% 2.22/1.37  Index Insertion      : 0.00
% 2.22/1.37  Index Deletion       : 0.00
% 2.66/1.37  Index Matching       : 0.00
% 2.66/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
