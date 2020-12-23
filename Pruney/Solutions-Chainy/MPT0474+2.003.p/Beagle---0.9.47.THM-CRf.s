%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:28 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   51 (  78 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 ( 109 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_3 > #skF_10 > #skF_2 > #skF_8 > #skF_7 > #skF_13 > #skF_12 > #skF_9 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_12',type,(
    '#skF_12': $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( B = k4_relat_1(A)
          <=> ! [C,D] :
                ( r2_hidden(k4_tarski(C,D),B)
              <=> r2_hidden(k4_tarski(D,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

tff(f_38,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_64,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_73,plain,(
    ! [A_57] :
      ( v1_relat_1(A_57)
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_77,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_73])).

tff(c_1693,plain,(
    ! [A_203,B_204] :
      ( r2_hidden(k4_tarski('#skF_9'(A_203,B_204),'#skF_8'(A_203,B_204)),A_203)
      | r2_hidden(k4_tarski('#skF_10'(A_203,B_204),'#skF_11'(A_203,B_204)),B_204)
      | k4_relat_1(A_203) = B_204
      | ~ v1_relat_1(B_204)
      | ~ v1_relat_1(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_115,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_3'(A_69,B_70),B_70)
      | ~ r2_hidden(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_310,plain,(
    ! [A_100,A_101,B_102] :
      ( r2_hidden('#skF_3'(A_100,k4_xboole_0(A_101,B_102)),A_101)
      | ~ r2_hidden(A_100,k4_xboole_0(A_101,B_102)) ) ),
    inference(resolution,[status(thm)],[c_115,c_6])).

tff(c_110,plain,(
    ! [D_64,B_65,A_66] :
      ( ~ r2_hidden(D_64,B_65)
      | ~ r2_hidden(D_64,k4_xboole_0(A_66,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_113,plain,(
    ! [D_64,A_7] :
      ( ~ r2_hidden(D_64,A_7)
      | ~ r2_hidden(D_64,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_110])).

tff(c_126,plain,(
    ! [A_69,B_70] :
      ( ~ r2_hidden('#skF_3'(A_69,B_70),k1_xboole_0)
      | ~ r2_hidden(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_115,c_113])).

tff(c_325,plain,(
    ! [A_100,B_102] : ~ r2_hidden(A_100,k4_xboole_0(k1_xboole_0,B_102)) ),
    inference(resolution,[status(thm)],[c_310,c_126])).

tff(c_344,plain,(
    ! [A_100] : ~ r2_hidden(A_100,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_325])).

tff(c_1722,plain,(
    ! [A_203] :
      ( r2_hidden(k4_tarski('#skF_9'(A_203,k1_xboole_0),'#skF_8'(A_203,k1_xboole_0)),A_203)
      | k4_relat_1(A_203) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_203) ) ),
    inference(resolution,[status(thm)],[c_1693,c_344])).

tff(c_1969,plain,(
    ! [A_226] :
      ( r2_hidden(k4_tarski('#skF_9'(A_226,k1_xboole_0),'#skF_8'(A_226,k1_xboole_0)),A_226)
      | k4_relat_1(A_226) = k1_xboole_0
      | ~ v1_relat_1(A_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1722])).

tff(c_1977,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1969,c_344])).

tff(c_1996,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1977])).

tff(c_1998,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1996])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.62  
% 3.13/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.62  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_3 > #skF_10 > #skF_2 > #skF_8 > #skF_7 > #skF_13 > #skF_12 > #skF_9 > #skF_5 > #skF_4
% 3.13/1.62  
% 3.13/1.62  %Foreground sorts:
% 3.13/1.62  
% 3.13/1.62  
% 3.13/1.62  %Background operators:
% 3.13/1.62  
% 3.13/1.62  
% 3.13/1.62  %Foreground operators:
% 3.13/1.62  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 3.13/1.62  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.13/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.13/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.13/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.13/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.13/1.62  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.13/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.13/1.62  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 3.13/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.13/1.62  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.13/1.62  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.13/1.62  tff('#skF_13', type, '#skF_13': $i > $i).
% 3.13/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.62  tff('#skF_12', type, '#skF_12': $i > $i).
% 3.13/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.13/1.62  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 3.13/1.62  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.13/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.13/1.62  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.13/1.62  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.13/1.62  
% 3.13/1.63  tff(f_96, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_relat_1)).
% 3.13/1.63  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.13/1.63  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.13/1.63  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => ((B = k4_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> r2_hidden(k4_tarski(D, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_relat_1)).
% 3.13/1.63  tff(f_38, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.13/1.63  tff(f_51, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 3.13/1.63  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.13/1.63  tff(c_64, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.13/1.63  tff(c_20, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.13/1.63  tff(c_73, plain, (![A_57]: (v1_relat_1(A_57) | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.13/1.63  tff(c_77, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_73])).
% 3.13/1.63  tff(c_1693, plain, (![A_203, B_204]: (r2_hidden(k4_tarski('#skF_9'(A_203, B_204), '#skF_8'(A_203, B_204)), A_203) | r2_hidden(k4_tarski('#skF_10'(A_203, B_204), '#skF_11'(A_203, B_204)), B_204) | k4_relat_1(A_203)=B_204 | ~v1_relat_1(B_204) | ~v1_relat_1(A_203))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.13/1.63  tff(c_22, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.13/1.63  tff(c_115, plain, (![A_69, B_70]: (r2_hidden('#skF_3'(A_69, B_70), B_70) | ~r2_hidden(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.13/1.63  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.13/1.63  tff(c_310, plain, (![A_100, A_101, B_102]: (r2_hidden('#skF_3'(A_100, k4_xboole_0(A_101, B_102)), A_101) | ~r2_hidden(A_100, k4_xboole_0(A_101, B_102)))), inference(resolution, [status(thm)], [c_115, c_6])).
% 3.13/1.63  tff(c_110, plain, (![D_64, B_65, A_66]: (~r2_hidden(D_64, B_65) | ~r2_hidden(D_64, k4_xboole_0(A_66, B_65)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.13/1.63  tff(c_113, plain, (![D_64, A_7]: (~r2_hidden(D_64, A_7) | ~r2_hidden(D_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_110])).
% 3.13/1.63  tff(c_126, plain, (![A_69, B_70]: (~r2_hidden('#skF_3'(A_69, B_70), k1_xboole_0) | ~r2_hidden(A_69, B_70))), inference(resolution, [status(thm)], [c_115, c_113])).
% 3.13/1.63  tff(c_325, plain, (![A_100, B_102]: (~r2_hidden(A_100, k4_xboole_0(k1_xboole_0, B_102)))), inference(resolution, [status(thm)], [c_310, c_126])).
% 3.13/1.63  tff(c_344, plain, (![A_100]: (~r2_hidden(A_100, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_325])).
% 3.13/1.63  tff(c_1722, plain, (![A_203]: (r2_hidden(k4_tarski('#skF_9'(A_203, k1_xboole_0), '#skF_8'(A_203, k1_xboole_0)), A_203) | k4_relat_1(A_203)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_203))), inference(resolution, [status(thm)], [c_1693, c_344])).
% 3.13/1.63  tff(c_1969, plain, (![A_226]: (r2_hidden(k4_tarski('#skF_9'(A_226, k1_xboole_0), '#skF_8'(A_226, k1_xboole_0)), A_226) | k4_relat_1(A_226)=k1_xboole_0 | ~v1_relat_1(A_226))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_1722])).
% 3.13/1.63  tff(c_1977, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_1969, c_344])).
% 3.13/1.63  tff(c_1996, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_77, c_1977])).
% 3.13/1.63  tff(c_1998, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_1996])).
% 3.13/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.63  
% 3.13/1.63  Inference rules
% 3.13/1.63  ----------------------
% 3.13/1.63  #Ref     : 0
% 3.13/1.63  #Sup     : 370
% 3.13/1.63  #Fact    : 0
% 3.13/1.63  #Define  : 0
% 3.13/1.63  #Split   : 0
% 3.13/1.63  #Chain   : 0
% 3.13/1.63  #Close   : 0
% 3.13/1.63  
% 3.13/1.63  Ordering : KBO
% 3.13/1.63  
% 3.13/1.63  Simplification rules
% 3.13/1.63  ----------------------
% 3.13/1.63  #Subsume      : 123
% 3.13/1.63  #Demod        : 335
% 3.13/1.63  #Tautology    : 83
% 3.13/1.63  #SimpNegUnit  : 10
% 3.13/1.63  #BackRed      : 17
% 3.13/1.63  
% 3.13/1.63  #Partial instantiations: 0
% 3.13/1.63  #Strategies tried      : 1
% 3.13/1.63  
% 3.13/1.63  Timing (in seconds)
% 3.13/1.63  ----------------------
% 3.13/1.63  Preprocessing        : 0.29
% 3.13/1.63  Parsing              : 0.15
% 3.13/1.63  CNF conversion       : 0.03
% 3.13/1.63  Main loop            : 0.49
% 3.13/1.63  Inferencing          : 0.18
% 3.13/1.63  Reduction            : 0.14
% 3.13/1.63  Demodulation         : 0.09
% 3.13/1.63  BG Simplification    : 0.03
% 3.13/1.63  Subsumption          : 0.10
% 3.13/1.63  Abstraction          : 0.03
% 3.13/1.63  MUC search           : 0.00
% 3.13/1.63  Cooper               : 0.00
% 3.13/1.63  Total                : 0.80
% 3.13/1.63  Index Insertion      : 0.00
% 3.13/1.63  Index Deletion       : 0.00
% 3.13/1.64  Index Matching       : 0.00
% 3.13/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
