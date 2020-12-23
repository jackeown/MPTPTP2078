%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:54 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   50 (  70 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 (  88 expanded)
%              Number of equality atoms :   19 (  40 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_36,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_72,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_92,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_1'(A_46,B_47),B_47)
      | r2_hidden('#skF_2'(A_46,B_47),A_46)
      | B_47 = A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_64,plain,(
    ! [A_34,B_35] : ~ r2_hidden(A_34,k2_zfmisc_1(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_67,plain,(
    ! [A_4] : ~ r2_hidden(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_64])).

tff(c_100,plain,(
    ! [B_47] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_47),B_47)
      | k1_xboole_0 = B_47 ) ),
    inference(resolution,[status(thm)],[c_92,c_67])).

tff(c_127,plain,(
    ! [C_55,A_56] :
      ( r2_hidden(k4_tarski(C_55,'#skF_6'(A_56,k1_relat_1(A_56),C_55)),A_56)
      | ~ r2_hidden(C_55,k1_relat_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_137,plain,(
    ! [C_57] : ~ r2_hidden(C_57,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_127,c_67])).

tff(c_149,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_100,c_137])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_149])).

tff(c_170,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_202,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_1'(A_69,B_70),B_70)
      | r2_hidden('#skF_2'(A_69,B_70),A_69)
      | B_70 = A_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_240,plain,(
    ! [B_74] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_74),B_74)
      | k1_xboole_0 = B_74 ) ),
    inference(resolution,[status(thm)],[c_202,c_67])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_37,plain,(
    ! [A_31] :
      ( v1_relat_1(A_31)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_41,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_37])).

tff(c_171,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_217,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_7'(A_71,B_72),k1_relat_1(B_72))
      | ~ r2_hidden(A_71,k2_relat_1(B_72))
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_220,plain,(
    ! [A_71] :
      ( r2_hidden('#skF_7'(A_71,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_71,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_217])).

tff(c_222,plain,(
    ! [A_71] :
      ( r2_hidden('#skF_7'(A_71,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_71,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_220])).

tff(c_223,plain,(
    ! [A_71] : ~ r2_hidden(A_71,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_222])).

tff(c_244,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_240,c_223])).

tff(c_255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_244])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.20  
% 1.92/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.20  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 1.92/1.20  
% 1.92/1.20  %Foreground sorts:
% 1.92/1.20  
% 1.92/1.20  
% 1.92/1.20  %Background operators:
% 1.92/1.20  
% 1.92/1.20  
% 1.92/1.20  %Foreground operators:
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.20  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.92/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.92/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.92/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.92/1.20  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 1.92/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.92/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.92/1.20  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.92/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.92/1.20  
% 1.92/1.21  tff(f_67, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.92/1.21  tff(f_33, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 1.92/1.21  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.92/1.21  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.92/1.21  tff(f_54, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.92/1.21  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.92/1.21  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.92/1.21  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 1.92/1.21  tff(c_36, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.92/1.21  tff(c_72, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 1.92/1.21  tff(c_92, plain, (![A_46, B_47]: (r2_hidden('#skF_1'(A_46, B_47), B_47) | r2_hidden('#skF_2'(A_46, B_47), A_46) | B_47=A_46)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.21  tff(c_14, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.21  tff(c_64, plain, (![A_34, B_35]: (~r2_hidden(A_34, k2_zfmisc_1(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.92/1.21  tff(c_67, plain, (![A_4]: (~r2_hidden(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_64])).
% 1.92/1.21  tff(c_100, plain, (![B_47]: (r2_hidden('#skF_1'(k1_xboole_0, B_47), B_47) | k1_xboole_0=B_47)), inference(resolution, [status(thm)], [c_92, c_67])).
% 1.92/1.21  tff(c_127, plain, (![C_55, A_56]: (r2_hidden(k4_tarski(C_55, '#skF_6'(A_56, k1_relat_1(A_56), C_55)), A_56) | ~r2_hidden(C_55, k1_relat_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.92/1.21  tff(c_137, plain, (![C_57]: (~r2_hidden(C_57, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_127, c_67])).
% 1.92/1.21  tff(c_149, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_100, c_137])).
% 1.92/1.21  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_149])).
% 1.92/1.21  tff(c_170, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 1.92/1.21  tff(c_202, plain, (![A_69, B_70]: (r2_hidden('#skF_1'(A_69, B_70), B_70) | r2_hidden('#skF_2'(A_69, B_70), A_69) | B_70=A_69)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.21  tff(c_240, plain, (![B_74]: (r2_hidden('#skF_1'(k1_xboole_0, B_74), B_74) | k1_xboole_0=B_74)), inference(resolution, [status(thm)], [c_202, c_67])).
% 1.92/1.21  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.92/1.21  tff(c_37, plain, (![A_31]: (v1_relat_1(A_31) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.92/1.21  tff(c_41, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_37])).
% 1.92/1.21  tff(c_171, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 1.92/1.21  tff(c_217, plain, (![A_71, B_72]: (r2_hidden('#skF_7'(A_71, B_72), k1_relat_1(B_72)) | ~r2_hidden(A_71, k2_relat_1(B_72)) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.92/1.21  tff(c_220, plain, (![A_71]: (r2_hidden('#skF_7'(A_71, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_71, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_171, c_217])).
% 1.92/1.21  tff(c_222, plain, (![A_71]: (r2_hidden('#skF_7'(A_71, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_71, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_220])).
% 1.92/1.21  tff(c_223, plain, (![A_71]: (~r2_hidden(A_71, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_67, c_222])).
% 1.92/1.21  tff(c_244, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_240, c_223])).
% 1.92/1.21  tff(c_255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_244])).
% 1.92/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.21  
% 1.92/1.21  Inference rules
% 1.92/1.21  ----------------------
% 1.92/1.21  #Ref     : 0
% 1.92/1.21  #Sup     : 40
% 1.92/1.21  #Fact    : 0
% 1.92/1.21  #Define  : 0
% 1.92/1.21  #Split   : 1
% 1.92/1.21  #Chain   : 0
% 1.92/1.21  #Close   : 0
% 1.92/1.21  
% 1.92/1.21  Ordering : KBO
% 1.92/1.21  
% 1.92/1.21  Simplification rules
% 1.92/1.21  ----------------------
% 1.92/1.21  #Subsume      : 5
% 1.92/1.21  #Demod        : 2
% 1.92/1.21  #Tautology    : 18
% 1.92/1.21  #SimpNegUnit  : 3
% 1.92/1.21  #BackRed      : 0
% 1.92/1.21  
% 1.92/1.21  #Partial instantiations: 0
% 1.92/1.21  #Strategies tried      : 1
% 1.92/1.21  
% 1.92/1.21  Timing (in seconds)
% 1.92/1.21  ----------------------
% 1.92/1.21  Preprocessing        : 0.27
% 1.92/1.21  Parsing              : 0.14
% 1.92/1.21  CNF conversion       : 0.02
% 1.92/1.21  Main loop            : 0.17
% 1.92/1.21  Inferencing          : 0.08
% 1.92/1.21  Reduction            : 0.04
% 1.92/1.21  Demodulation         : 0.03
% 1.92/1.21  BG Simplification    : 0.01
% 1.92/1.21  Subsumption          : 0.03
% 1.92/1.21  Abstraction          : 0.01
% 1.92/1.21  MUC search           : 0.00
% 1.92/1.21  Cooper               : 0.00
% 1.92/1.21  Total                : 0.46
% 1.92/1.21  Index Insertion      : 0.00
% 1.92/1.21  Index Deletion       : 0.00
% 1.92/1.21  Index Matching       : 0.00
% 1.92/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
