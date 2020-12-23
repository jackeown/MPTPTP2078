%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:22 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   52 (  74 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 ( 111 expanded)
%              Number of equality atoms :   18 (  35 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_53,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_65,plain,(
    ! [C_30,B_31] : ~ r2_hidden(C_30,k4_xboole_0(B_31,k1_tarski(C_30))) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_68,plain,(
    ! [C_30] : ~ r2_hidden(C_30,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_65])).

tff(c_40,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | k11_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_70,plain,(
    k11_relat_1('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_32,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_241,plain,(
    ! [A_69,B_70] :
      ( r2_hidden(k4_tarski('#skF_1'(A_69,B_70),'#skF_2'(A_69,B_70)),A_69)
      | r2_hidden('#skF_3'(A_69,B_70),B_70)
      | k1_relat_1(A_69) = B_70 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_270,plain,(
    ! [B_70] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_70),B_70)
      | k1_relat_1(k1_xboole_0) = B_70 ) ),
    inference(resolution,[status(thm)],[c_241,c_68])).

tff(c_280,plain,(
    ! [B_71] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_71),B_71)
      | k1_xboole_0 = B_71 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_270])).

tff(c_106,plain,(
    ! [A_45,B_46,C_47] :
      ( r2_hidden(k4_tarski(A_45,B_46),C_47)
      | ~ r2_hidden(B_46,k11_relat_1(C_47,A_45))
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k1_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(C_21,D_24),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_126,plain,(
    ! [A_45,C_47,B_46] :
      ( r2_hidden(A_45,k1_relat_1(C_47))
      | ~ r2_hidden(B_46,k11_relat_1(C_47,A_45))
      | ~ v1_relat_1(C_47) ) ),
    inference(resolution,[status(thm)],[c_106,c_14])).

tff(c_311,plain,(
    ! [A_72,C_73] :
      ( r2_hidden(A_72,k1_relat_1(C_73))
      | ~ v1_relat_1(C_73)
      | k11_relat_1(C_73,A_72) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_280,c_126])).

tff(c_34,plain,
    ( k11_relat_1('#skF_6','#skF_5') = k1_xboole_0
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_71,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_34])).

tff(c_337,plain,
    ( ~ v1_relat_1('#skF_6')
    | k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_311,c_71])).

tff(c_349,plain,(
    k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_337])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_349])).

tff(c_352,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_355,plain,(
    k11_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_34])).

tff(c_444,plain,(
    ! [C_94,A_95] :
      ( r2_hidden(k4_tarski(C_94,'#skF_4'(A_95,k1_relat_1(A_95),C_94)),A_95)
      | ~ r2_hidden(C_94,k1_relat_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    ! [B_26,C_27,A_25] :
      ( r2_hidden(B_26,k11_relat_1(C_27,A_25))
      | ~ r2_hidden(k4_tarski(A_25,B_26),C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1118,plain,(
    ! [A_138,C_139] :
      ( r2_hidden('#skF_4'(A_138,k1_relat_1(A_138),C_139),k11_relat_1(A_138,C_139))
      | ~ v1_relat_1(A_138)
      | ~ r2_hidden(C_139,k1_relat_1(A_138)) ) ),
    inference(resolution,[status(thm)],[c_444,c_26])).

tff(c_1135,plain,
    ( r2_hidden('#skF_4'('#skF_6',k1_relat_1('#skF_6'),'#skF_5'),k1_xboole_0)
    | ~ v1_relat_1('#skF_6')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_1118])).

tff(c_1142,plain,(
    r2_hidden('#skF_4'('#skF_6',k1_relat_1('#skF_6'),'#skF_5'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_32,c_1135])).

tff(c_1144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:58:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.40  
% 2.74/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.40  %$ r2_hidden > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.74/1.40  
% 2.74/1.40  %Foreground sorts:
% 2.74/1.40  
% 2.74/1.40  
% 2.74/1.40  %Background operators:
% 2.74/1.40  
% 2.74/1.40  
% 2.74/1.40  %Foreground operators:
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.74/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.74/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.74/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.74/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.74/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.74/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.74/1.40  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.74/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.74/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.74/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.74/1.41  
% 2.74/1.41  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.74/1.41  tff(f_36, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.74/1.41  tff(f_61, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.74/1.41  tff(f_53, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.74/1.41  tff(f_44, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.74/1.41  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.74/1.41  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.74/1.41  tff(c_65, plain, (![C_30, B_31]: (~r2_hidden(C_30, k4_xboole_0(B_31, k1_tarski(C_30))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.74/1.41  tff(c_68, plain, (![C_30]: (~r2_hidden(C_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_65])).
% 2.74/1.41  tff(c_40, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6')) | k11_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.74/1.41  tff(c_70, plain, (k11_relat_1('#skF_6', '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 2.74/1.41  tff(c_32, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.74/1.41  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.74/1.41  tff(c_241, plain, (![A_69, B_70]: (r2_hidden(k4_tarski('#skF_1'(A_69, B_70), '#skF_2'(A_69, B_70)), A_69) | r2_hidden('#skF_3'(A_69, B_70), B_70) | k1_relat_1(A_69)=B_70)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.74/1.41  tff(c_270, plain, (![B_70]: (r2_hidden('#skF_3'(k1_xboole_0, B_70), B_70) | k1_relat_1(k1_xboole_0)=B_70)), inference(resolution, [status(thm)], [c_241, c_68])).
% 2.74/1.41  tff(c_280, plain, (![B_71]: (r2_hidden('#skF_3'(k1_xboole_0, B_71), B_71) | k1_xboole_0=B_71)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_270])).
% 2.74/1.41  tff(c_106, plain, (![A_45, B_46, C_47]: (r2_hidden(k4_tarski(A_45, B_46), C_47) | ~r2_hidden(B_46, k11_relat_1(C_47, A_45)) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.74/1.41  tff(c_14, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k1_relat_1(A_6)) | ~r2_hidden(k4_tarski(C_21, D_24), A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.74/1.41  tff(c_126, plain, (![A_45, C_47, B_46]: (r2_hidden(A_45, k1_relat_1(C_47)) | ~r2_hidden(B_46, k11_relat_1(C_47, A_45)) | ~v1_relat_1(C_47))), inference(resolution, [status(thm)], [c_106, c_14])).
% 2.74/1.41  tff(c_311, plain, (![A_72, C_73]: (r2_hidden(A_72, k1_relat_1(C_73)) | ~v1_relat_1(C_73) | k11_relat_1(C_73, A_72)=k1_xboole_0)), inference(resolution, [status(thm)], [c_280, c_126])).
% 2.74/1.41  tff(c_34, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0 | ~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.74/1.41  tff(c_71, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_70, c_34])).
% 2.74/1.41  tff(c_337, plain, (~v1_relat_1('#skF_6') | k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_311, c_71])).
% 2.74/1.41  tff(c_349, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_337])).
% 2.74/1.41  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_349])).
% 2.74/1.41  tff(c_352, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_40])).
% 2.74/1.41  tff(c_355, plain, (k11_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_352, c_34])).
% 2.74/1.42  tff(c_444, plain, (![C_94, A_95]: (r2_hidden(k4_tarski(C_94, '#skF_4'(A_95, k1_relat_1(A_95), C_94)), A_95) | ~r2_hidden(C_94, k1_relat_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.74/1.42  tff(c_26, plain, (![B_26, C_27, A_25]: (r2_hidden(B_26, k11_relat_1(C_27, A_25)) | ~r2_hidden(k4_tarski(A_25, B_26), C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.74/1.42  tff(c_1118, plain, (![A_138, C_139]: (r2_hidden('#skF_4'(A_138, k1_relat_1(A_138), C_139), k11_relat_1(A_138, C_139)) | ~v1_relat_1(A_138) | ~r2_hidden(C_139, k1_relat_1(A_138)))), inference(resolution, [status(thm)], [c_444, c_26])).
% 2.74/1.42  tff(c_1135, plain, (r2_hidden('#skF_4'('#skF_6', k1_relat_1('#skF_6'), '#skF_5'), k1_xboole_0) | ~v1_relat_1('#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_355, c_1118])).
% 2.74/1.42  tff(c_1142, plain, (r2_hidden('#skF_4'('#skF_6', k1_relat_1('#skF_6'), '#skF_5'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_352, c_32, c_1135])).
% 2.74/1.42  tff(c_1144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1142])).
% 2.74/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.42  
% 2.74/1.42  Inference rules
% 2.74/1.42  ----------------------
% 2.74/1.42  #Ref     : 0
% 2.74/1.42  #Sup     : 237
% 2.74/1.42  #Fact    : 0
% 2.74/1.42  #Define  : 0
% 2.74/1.42  #Split   : 3
% 2.74/1.42  #Chain   : 0
% 2.74/1.42  #Close   : 0
% 2.74/1.42  
% 2.74/1.42  Ordering : KBO
% 2.74/1.42  
% 2.74/1.42  Simplification rules
% 2.74/1.42  ----------------------
% 2.74/1.42  #Subsume      : 51
% 2.74/1.42  #Demod        : 78
% 2.74/1.42  #Tautology    : 52
% 2.74/1.42  #SimpNegUnit  : 38
% 2.74/1.42  #BackRed      : 0
% 2.74/1.42  
% 2.74/1.42  #Partial instantiations: 0
% 2.74/1.42  #Strategies tried      : 1
% 2.74/1.42  
% 2.74/1.42  Timing (in seconds)
% 2.74/1.42  ----------------------
% 2.74/1.42  Preprocessing        : 0.29
% 2.74/1.42  Parsing              : 0.15
% 2.74/1.42  CNF conversion       : 0.02
% 2.74/1.42  Main loop            : 0.39
% 2.74/1.42  Inferencing          : 0.15
% 2.74/1.42  Reduction            : 0.10
% 2.74/1.42  Demodulation         : 0.06
% 2.74/1.42  BG Simplification    : 0.02
% 2.74/1.42  Subsumption          : 0.09
% 2.74/1.42  Abstraction          : 0.03
% 2.74/1.42  MUC search           : 0.00
% 2.74/1.42  Cooper               : 0.00
% 2.74/1.42  Total                : 0.70
% 2.74/1.42  Index Insertion      : 0.00
% 2.74/1.42  Index Deletion       : 0.00
% 2.74/1.42  Index Matching       : 0.00
% 2.74/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
