%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:17 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :   40 (  50 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 ( 107 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r1_tarski(A,B)
         => ( k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A)
            & k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(k7_relat_1(B,A),A) = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C,D] :
              ( ( r1_tarski(C,D)
                & k7_relat_1(A,D) = k7_relat_1(B,D) )
             => k7_relat_1(A,C) = k7_relat_1(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t188_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k7_relat_1(A_4,B_5))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(k7_relat_1(B_7,A_6),A_6) = k7_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_236,plain,(
    ! [B_54,C_55,A_56,D_57] :
      ( k7_relat_1(B_54,C_55) = k7_relat_1(A_56,C_55)
      | k7_relat_1(B_54,D_57) != k7_relat_1(A_56,D_57)
      | ~ r1_tarski(C_55,D_57)
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_242,plain,(
    ! [B_7,A_6,C_55,A_56] :
      ( k7_relat_1(k7_relat_1(B_7,A_6),C_55) = k7_relat_1(A_56,C_55)
      | k7_relat_1(B_7,A_6) != k7_relat_1(A_56,A_6)
      | ~ r1_tarski(C_55,A_6)
      | ~ v1_relat_1(k7_relat_1(B_7,A_6))
      | ~ v1_relat_1(A_56)
      | ~ v1_relat_1(B_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_236])).

tff(c_1206,plain,(
    ! [A_117,A_118,C_119] :
      ( k7_relat_1(k7_relat_1(A_117,A_118),C_119) = k7_relat_1(A_117,C_119)
      | ~ r1_tarski(C_119,A_118)
      | ~ v1_relat_1(k7_relat_1(A_117,A_118))
      | ~ v1_relat_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_242])).

tff(c_1942,plain,(
    ! [A_141,B_142,C_143] :
      ( k7_relat_1(k7_relat_1(A_141,B_142),C_143) = k7_relat_1(A_141,C_143)
      | ~ r1_tarski(C_143,B_142)
      | ~ v1_relat_1(A_141) ) ),
    inference(resolution,[status(thm)],[c_4,c_1206])).

tff(c_10,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_20,A_19)),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_23,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_tarski(A_27,C_28)
      | ~ r1_tarski(B_29,C_28)
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29,plain,(
    ! [A_27] :
      ( r1_tarski(A_27,'#skF_2')
      | ~ r1_tarski(A_27,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_23])).

tff(c_69,plain,(
    ! [B_35,A_36] :
      ( k7_relat_1(B_35,A_36) = B_35
      | ~ r1_tarski(k1_relat_1(B_35),A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_79,plain,(
    ! [B_37] :
      ( k7_relat_1(B_37,'#skF_2') = B_37
      | ~ v1_relat_1(B_37)
      | ~ r1_tarski(k1_relat_1(B_37),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_29,c_69])).

tff(c_145,plain,(
    ! [B_50] :
      ( k7_relat_1(k7_relat_1(B_50,'#skF_1'),'#skF_2') = k7_relat_1(B_50,'#skF_1')
      | ~ v1_relat_1(k7_relat_1(B_50,'#skF_1'))
      | ~ v1_relat_1(B_50) ) ),
    inference(resolution,[status(thm)],[c_10,c_79])).

tff(c_155,plain,(
    ! [A_51] :
      ( k7_relat_1(k7_relat_1(A_51,'#skF_1'),'#skF_2') = k7_relat_1(A_51,'#skF_1')
      | ~ v1_relat_1(A_51) ) ),
    inference(resolution,[status(thm)],[c_4,c_145])).

tff(c_14,plain,
    ( k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1')
    | k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_68,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_174,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_68])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_174])).

tff(c_196,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_2116,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1942,c_196])).

tff(c_2197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_2116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:06:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.82  
% 4.60/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.82  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.60/1.82  
% 4.60/1.82  %Foreground sorts:
% 4.60/1.82  
% 4.60/1.82  
% 4.60/1.82  %Background operators:
% 4.60/1.82  
% 4.60/1.82  
% 4.60/1.82  %Foreground operators:
% 4.60/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.60/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.82  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.60/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.60/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.60/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.60/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.60/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.60/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.60/1.82  
% 4.60/1.83  tff(f_72, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r1_tarski(A, B) => ((k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A)) & (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_funct_1)).
% 4.60/1.83  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.60/1.83  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(k7_relat_1(B, A), A) = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_relat_1)).
% 4.60/1.83  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C, D]: ((r1_tarski(C, D) & (k7_relat_1(A, D) = k7_relat_1(B, D))) => (k7_relat_1(A, C) = k7_relat_1(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t188_relat_1)).
% 4.60/1.83  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 4.60/1.83  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.60/1.83  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 4.60/1.83  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.60/1.83  tff(c_16, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.60/1.83  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k7_relat_1(A_4, B_5)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.60/1.83  tff(c_6, plain, (![B_7, A_6]: (k7_relat_1(k7_relat_1(B_7, A_6), A_6)=k7_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.60/1.83  tff(c_236, plain, (![B_54, C_55, A_56, D_57]: (k7_relat_1(B_54, C_55)=k7_relat_1(A_56, C_55) | k7_relat_1(B_54, D_57)!=k7_relat_1(A_56, D_57) | ~r1_tarski(C_55, D_57) | ~v1_relat_1(B_54) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.60/1.83  tff(c_242, plain, (![B_7, A_6, C_55, A_56]: (k7_relat_1(k7_relat_1(B_7, A_6), C_55)=k7_relat_1(A_56, C_55) | k7_relat_1(B_7, A_6)!=k7_relat_1(A_56, A_6) | ~r1_tarski(C_55, A_6) | ~v1_relat_1(k7_relat_1(B_7, A_6)) | ~v1_relat_1(A_56) | ~v1_relat_1(B_7))), inference(superposition, [status(thm), theory('equality')], [c_6, c_236])).
% 4.60/1.83  tff(c_1206, plain, (![A_117, A_118, C_119]: (k7_relat_1(k7_relat_1(A_117, A_118), C_119)=k7_relat_1(A_117, C_119) | ~r1_tarski(C_119, A_118) | ~v1_relat_1(k7_relat_1(A_117, A_118)) | ~v1_relat_1(A_117) | ~v1_relat_1(A_117))), inference(reflexivity, [status(thm), theory('equality')], [c_242])).
% 4.60/1.83  tff(c_1942, plain, (![A_141, B_142, C_143]: (k7_relat_1(k7_relat_1(A_141, B_142), C_143)=k7_relat_1(A_141, C_143) | ~r1_tarski(C_143, B_142) | ~v1_relat_1(A_141))), inference(resolution, [status(thm)], [c_4, c_1206])).
% 4.60/1.83  tff(c_10, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(k7_relat_1(B_20, A_19)), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.60/1.83  tff(c_23, plain, (![A_27, C_28, B_29]: (r1_tarski(A_27, C_28) | ~r1_tarski(B_29, C_28) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.60/1.83  tff(c_29, plain, (![A_27]: (r1_tarski(A_27, '#skF_2') | ~r1_tarski(A_27, '#skF_1'))), inference(resolution, [status(thm)], [c_16, c_23])).
% 4.60/1.83  tff(c_69, plain, (![B_35, A_36]: (k7_relat_1(B_35, A_36)=B_35 | ~r1_tarski(k1_relat_1(B_35), A_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.60/1.83  tff(c_79, plain, (![B_37]: (k7_relat_1(B_37, '#skF_2')=B_37 | ~v1_relat_1(B_37) | ~r1_tarski(k1_relat_1(B_37), '#skF_1'))), inference(resolution, [status(thm)], [c_29, c_69])).
% 4.60/1.83  tff(c_145, plain, (![B_50]: (k7_relat_1(k7_relat_1(B_50, '#skF_1'), '#skF_2')=k7_relat_1(B_50, '#skF_1') | ~v1_relat_1(k7_relat_1(B_50, '#skF_1')) | ~v1_relat_1(B_50))), inference(resolution, [status(thm)], [c_10, c_79])).
% 4.60/1.83  tff(c_155, plain, (![A_51]: (k7_relat_1(k7_relat_1(A_51, '#skF_1'), '#skF_2')=k7_relat_1(A_51, '#skF_1') | ~v1_relat_1(A_51))), inference(resolution, [status(thm)], [c_4, c_145])).
% 4.60/1.83  tff(c_14, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1') | k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.60/1.83  tff(c_68, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_14])).
% 4.60/1.83  tff(c_174, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_155, c_68])).
% 4.60/1.83  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_174])).
% 4.60/1.83  tff(c_196, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_14])).
% 4.60/1.83  tff(c_2116, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1942, c_196])).
% 4.60/1.83  tff(c_2197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_2116])).
% 4.60/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.83  
% 4.60/1.83  Inference rules
% 4.60/1.83  ----------------------
% 4.60/1.83  #Ref     : 4
% 4.60/1.83  #Sup     : 529
% 4.60/1.83  #Fact    : 0
% 4.60/1.83  #Define  : 0
% 4.60/1.83  #Split   : 5
% 4.60/1.83  #Chain   : 0
% 4.60/1.83  #Close   : 0
% 4.60/1.83  
% 4.60/1.83  Ordering : KBO
% 4.60/1.83  
% 4.60/1.83  Simplification rules
% 4.60/1.83  ----------------------
% 4.60/1.83  #Subsume      : 148
% 4.60/1.83  #Demod        : 284
% 4.60/1.83  #Tautology    : 91
% 4.60/1.83  #SimpNegUnit  : 9
% 4.60/1.83  #BackRed      : 0
% 4.60/1.83  
% 4.60/1.83  #Partial instantiations: 0
% 4.60/1.83  #Strategies tried      : 1
% 4.60/1.83  
% 4.60/1.83  Timing (in seconds)
% 4.60/1.83  ----------------------
% 4.60/1.84  Preprocessing        : 0.29
% 4.60/1.84  Parsing              : 0.16
% 4.60/1.84  CNF conversion       : 0.02
% 4.60/1.84  Main loop            : 0.80
% 4.60/1.84  Inferencing          : 0.28
% 4.60/1.84  Reduction            : 0.23
% 4.60/1.84  Demodulation         : 0.16
% 4.60/1.84  BG Simplification    : 0.04
% 4.60/1.84  Subsumption          : 0.20
% 4.60/1.84  Abstraction          : 0.05
% 4.60/1.84  MUC search           : 0.00
% 4.60/1.84  Cooper               : 0.00
% 4.60/1.84  Total                : 1.12
% 4.60/1.84  Index Insertion      : 0.00
% 4.60/1.84  Index Deletion       : 0.00
% 4.60/1.84  Index Matching       : 0.00
% 4.60/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
