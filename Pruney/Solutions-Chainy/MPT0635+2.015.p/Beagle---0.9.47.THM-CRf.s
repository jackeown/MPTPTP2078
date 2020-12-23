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
% DateTime   : Thu Dec  3 10:03:22 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   46 (  64 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 ( 113 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_42,plain,(
    r2_hidden('#skF_4',k3_xboole_0(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_85,plain,(
    ! [D_26,B_27,A_28] :
      ( r2_hidden(D_26,B_27)
      | ~ r2_hidden(D_26,k3_xboole_0(A_28,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_89,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_85])).

tff(c_26,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    ! [A_10] : v1_funct_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_36,plain,(
    ! [A_15,C_19] :
      ( k1_funct_1(k6_relat_1(A_15),C_19) = C_19
      | ~ r2_hidden(C_19,A_15)
      | ~ v1_funct_1(k6_relat_1(A_15))
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_50,plain,(
    ! [A_15,C_19] :
      ( k1_funct_1(k6_relat_1(A_15),C_19) = C_19
      | ~ r2_hidden(C_19,A_15)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_36])).

tff(c_52,plain,(
    ! [A_15,C_19] :
      ( k1_funct_1(k6_relat_1(A_15),C_19) = C_19
      | ~ r2_hidden(C_19,A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_50])).

tff(c_46,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,(
    ! [A_15] :
      ( k1_relat_1(k6_relat_1(A_15)) = A_15
      | ~ v1_funct_1(k6_relat_1(A_15))
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,(
    ! [A_15] :
      ( k1_relat_1(k6_relat_1(A_15)) = A_15
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_54,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_48])).

tff(c_274,plain,(
    ! [B_67,C_68,A_69] :
      ( k1_funct_1(k5_relat_1(B_67,C_68),A_69) = k1_funct_1(C_68,k1_funct_1(B_67,A_69))
      | ~ r2_hidden(A_69,k1_relat_1(B_67))
      | ~ v1_funct_1(C_68)
      | ~ v1_relat_1(C_68)
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_310,plain,(
    ! [A_15,C_68,A_69] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_15),C_68),A_69) = k1_funct_1(C_68,k1_funct_1(k6_relat_1(A_15),A_69))
      | ~ r2_hidden(A_69,A_15)
      | ~ v1_funct_1(C_68)
      | ~ v1_relat_1(C_68)
      | ~ v1_funct_1(k6_relat_1(A_15))
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_274])).

tff(c_561,plain,(
    ! [A_87,C_88,A_89] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_87),C_88),A_89) = k1_funct_1(C_88,k1_funct_1(k6_relat_1(A_87),A_89))
      | ~ r2_hidden(A_89,A_87)
      | ~ v1_funct_1(C_88)
      | ~ v1_relat_1(C_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_310])).

tff(c_40,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_5'),'#skF_6'),'#skF_4') != k1_funct_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_571,plain,
    ( k1_funct_1('#skF_6',k1_funct_1(k6_relat_1('#skF_5'),'#skF_4')) != k1_funct_1('#skF_6','#skF_4')
    | ~ r2_hidden('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_40])).

tff(c_577,plain,(
    k1_funct_1('#skF_6',k1_funct_1(k6_relat_1('#skF_5'),'#skF_4')) != k1_funct_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_89,c_571])).

tff(c_581,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_577])).

tff(c_585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_581])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.41  
% 2.66/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.41  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.66/1.41  
% 2.66/1.41  %Foreground sorts:
% 2.66/1.41  
% 2.66/1.41  
% 2.66/1.41  %Background operators:
% 2.66/1.41  
% 2.66/1.41  
% 2.66/1.41  %Foreground operators:
% 2.66/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.66/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.66/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.66/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.66/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.66/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.66/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.66/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.66/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.66/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.66/1.41  
% 2.66/1.42  tff(f_79, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_1)).
% 2.66/1.42  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.66/1.42  tff(f_44, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.66/1.42  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.66/1.42  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 2.66/1.42  tff(c_42, plain, (r2_hidden('#skF_4', k3_xboole_0(k1_relat_1('#skF_6'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.66/1.42  tff(c_85, plain, (![D_26, B_27, A_28]: (r2_hidden(D_26, B_27) | ~r2_hidden(D_26, k3_xboole_0(A_28, B_27)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.66/1.42  tff(c_89, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_85])).
% 2.66/1.42  tff(c_26, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.66/1.42  tff(c_28, plain, (![A_10]: (v1_funct_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.66/1.42  tff(c_36, plain, (![A_15, C_19]: (k1_funct_1(k6_relat_1(A_15), C_19)=C_19 | ~r2_hidden(C_19, A_15) | ~v1_funct_1(k6_relat_1(A_15)) | ~v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.66/1.42  tff(c_50, plain, (![A_15, C_19]: (k1_funct_1(k6_relat_1(A_15), C_19)=C_19 | ~r2_hidden(C_19, A_15) | ~v1_relat_1(k6_relat_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_36])).
% 2.66/1.42  tff(c_52, plain, (![A_15, C_19]: (k1_funct_1(k6_relat_1(A_15), C_19)=C_19 | ~r2_hidden(C_19, A_15))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_50])).
% 2.66/1.42  tff(c_46, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.66/1.42  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.66/1.42  tff(c_38, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15 | ~v1_funct_1(k6_relat_1(A_15)) | ~v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.66/1.42  tff(c_48, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15 | ~v1_relat_1(k6_relat_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38])).
% 2.66/1.42  tff(c_54, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_48])).
% 2.66/1.42  tff(c_274, plain, (![B_67, C_68, A_69]: (k1_funct_1(k5_relat_1(B_67, C_68), A_69)=k1_funct_1(C_68, k1_funct_1(B_67, A_69)) | ~r2_hidden(A_69, k1_relat_1(B_67)) | ~v1_funct_1(C_68) | ~v1_relat_1(C_68) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.66/1.42  tff(c_310, plain, (![A_15, C_68, A_69]: (k1_funct_1(k5_relat_1(k6_relat_1(A_15), C_68), A_69)=k1_funct_1(C_68, k1_funct_1(k6_relat_1(A_15), A_69)) | ~r2_hidden(A_69, A_15) | ~v1_funct_1(C_68) | ~v1_relat_1(C_68) | ~v1_funct_1(k6_relat_1(A_15)) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_274])).
% 2.66/1.42  tff(c_561, plain, (![A_87, C_88, A_89]: (k1_funct_1(k5_relat_1(k6_relat_1(A_87), C_88), A_89)=k1_funct_1(C_88, k1_funct_1(k6_relat_1(A_87), A_89)) | ~r2_hidden(A_89, A_87) | ~v1_funct_1(C_88) | ~v1_relat_1(C_88))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_310])).
% 2.66/1.42  tff(c_40, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_5'), '#skF_6'), '#skF_4')!=k1_funct_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.66/1.42  tff(c_571, plain, (k1_funct_1('#skF_6', k1_funct_1(k6_relat_1('#skF_5'), '#skF_4'))!=k1_funct_1('#skF_6', '#skF_4') | ~r2_hidden('#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_561, c_40])).
% 2.66/1.42  tff(c_577, plain, (k1_funct_1('#skF_6', k1_funct_1(k6_relat_1('#skF_5'), '#skF_4'))!=k1_funct_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_89, c_571])).
% 2.66/1.42  tff(c_581, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_52, c_577])).
% 2.66/1.42  tff(c_585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_581])).
% 2.66/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.42  
% 2.66/1.42  Inference rules
% 2.66/1.42  ----------------------
% 2.66/1.42  #Ref     : 0
% 2.66/1.42  #Sup     : 111
% 2.66/1.42  #Fact    : 0
% 2.66/1.42  #Define  : 0
% 2.66/1.42  #Split   : 0
% 2.66/1.42  #Chain   : 0
% 2.66/1.42  #Close   : 0
% 2.66/1.42  
% 2.66/1.42  Ordering : KBO
% 2.66/1.42  
% 2.66/1.42  Simplification rules
% 2.66/1.42  ----------------------
% 2.66/1.42  #Subsume      : 17
% 2.66/1.42  #Demod        : 63
% 2.66/1.42  #Tautology    : 30
% 2.66/1.42  #SimpNegUnit  : 0
% 2.66/1.42  #BackRed      : 0
% 2.66/1.42  
% 2.66/1.42  #Partial instantiations: 0
% 2.66/1.42  #Strategies tried      : 1
% 2.66/1.42  
% 2.66/1.42  Timing (in seconds)
% 2.66/1.42  ----------------------
% 2.66/1.42  Preprocessing        : 0.31
% 2.66/1.42  Parsing              : 0.16
% 2.66/1.42  CNF conversion       : 0.02
% 2.66/1.42  Main loop            : 0.35
% 2.66/1.42  Inferencing          : 0.14
% 2.66/1.42  Reduction            : 0.09
% 2.66/1.42  Demodulation         : 0.07
% 2.66/1.42  BG Simplification    : 0.02
% 2.66/1.42  Subsumption          : 0.08
% 2.66/1.42  Abstraction          : 0.02
% 2.66/1.42  MUC search           : 0.00
% 2.66/1.42  Cooper               : 0.00
% 2.66/1.42  Total                : 0.68
% 2.66/1.42  Index Insertion      : 0.00
% 2.66/1.42  Index Deletion       : 0.00
% 2.66/1.42  Index Matching       : 0.00
% 2.66/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
