%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:17 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   44 (  65 expanded)
%              Number of leaves         :   22 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :   83 ( 168 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( r2_hidden(A,k2_relat_1(k5_relat_1(C,B)))
             => r2_hidden(A,k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24,plain,(
    r2_hidden('#skF_2',k2_relat_1(k5_relat_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [B_9,A_7] :
      ( k9_relat_1(B_9,k2_relat_1(A_7)) = k2_relat_1(k5_relat_1(A_7,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),k1_relat_1(C_3))
      | ~ r2_hidden(A_1,k9_relat_1(C_3,B_2))
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_2,C_3),A_1),C_3)
      | ~ r2_hidden(A_1,k9_relat_1(C_3,B_2))
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_48,plain,(
    ! [A_35,B_36,C_37] :
      ( k1_funct_1(A_35,B_36) = C_37
      | ~ r2_hidden(k4_tarski(B_36,C_37),A_35)
      | ~ r2_hidden(B_36,k1_relat_1(A_35))
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_98,plain,(
    ! [C_44,A_45,B_46] :
      ( k1_funct_1(C_44,'#skF_1'(A_45,B_46,C_44)) = A_45
      | ~ r2_hidden('#skF_1'(A_45,B_46,C_44),k1_relat_1(C_44))
      | ~ v1_funct_1(C_44)
      | ~ r2_hidden(A_45,k9_relat_1(C_44,B_46))
      | ~ v1_relat_1(C_44) ) ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_113,plain,(
    ! [C_47,A_48,B_49] :
      ( k1_funct_1(C_47,'#skF_1'(A_48,B_49,C_47)) = A_48
      | ~ v1_funct_1(C_47)
      | ~ r2_hidden(A_48,k9_relat_1(C_47,B_49))
      | ~ v1_relat_1(C_47) ) ),
    inference(resolution,[status(thm)],[c_8,c_98])).

tff(c_146,plain,(
    ! [B_52,A_53,A_54] :
      ( k1_funct_1(B_52,'#skF_1'(A_53,k2_relat_1(A_54),B_52)) = A_53
      | ~ v1_funct_1(B_52)
      | ~ r2_hidden(A_53,k2_relat_1(k5_relat_1(A_54,B_52)))
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_113])).

tff(c_160,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_2',k2_relat_1('#skF_4'),'#skF_3')) = '#skF_2'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_146])).

tff(c_167,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_2',k2_relat_1('#skF_4'),'#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_30,c_160])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( r2_hidden(k1_funct_1(B_16,A_15),k2_relat_1(B_16))
      | ~ r2_hidden(A_15,k1_relat_1(B_16))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_174,plain,
    ( r2_hidden('#skF_2',k2_relat_1('#skF_3'))
    | ~ r2_hidden('#skF_1'('#skF_2',k2_relat_1('#skF_4'),'#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_20])).

tff(c_180,plain,
    ( r2_hidden('#skF_2',k2_relat_1('#skF_3'))
    | ~ r2_hidden('#skF_1'('#skF_2',k2_relat_1('#skF_4'),'#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_174])).

tff(c_181,plain,(
    ~ r2_hidden('#skF_1'('#skF_2',k2_relat_1('#skF_4'),'#skF_3'),k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_180])).

tff(c_185,plain,
    ( ~ r2_hidden('#skF_2',k9_relat_1('#skF_3',k2_relat_1('#skF_4')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_181])).

tff(c_191,plain,(
    ~ r2_hidden('#skF_2',k9_relat_1('#skF_3',k2_relat_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_185])).

tff(c_202,plain,
    ( ~ r2_hidden('#skF_2',k2_relat_1(k5_relat_1('#skF_4','#skF_3')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_191])).

tff(c_205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_24,c_202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.39  
% 2.37/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.40  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.37/1.40  
% 2.37/1.40  %Foreground sorts:
% 2.37/1.40  
% 2.37/1.40  
% 2.37/1.40  %Background operators:
% 2.37/1.40  
% 2.37/1.40  
% 2.37/1.40  %Foreground operators:
% 2.37/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.37/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.37/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.37/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.37/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.37/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.37/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.37/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.40  
% 2.37/1.41  tff(f_83, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k2_relat_1(k5_relat_1(C, B))) => r2_hidden(A, k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_funct_1)).
% 2.37/1.41  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.37/1.41  tff(f_36, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.37/1.41  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 2.37/1.41  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 2.37/1.41  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.37/1.41  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.37/1.41  tff(c_24, plain, (r2_hidden('#skF_2', k2_relat_1(k5_relat_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.37/1.41  tff(c_10, plain, (![B_9, A_7]: (k9_relat_1(B_9, k2_relat_1(A_7))=k2_relat_1(k5_relat_1(A_7, B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.37/1.41  tff(c_8, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), k1_relat_1(C_3)) | ~r2_hidden(A_1, k9_relat_1(C_3, B_2)) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.37/1.41  tff(c_22, plain, (~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.37/1.41  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.37/1.41  tff(c_6, plain, (![A_1, B_2, C_3]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_2, C_3), A_1), C_3) | ~r2_hidden(A_1, k9_relat_1(C_3, B_2)) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.37/1.41  tff(c_48, plain, (![A_35, B_36, C_37]: (k1_funct_1(A_35, B_36)=C_37 | ~r2_hidden(k4_tarski(B_36, C_37), A_35) | ~r2_hidden(B_36, k1_relat_1(A_35)) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.37/1.41  tff(c_98, plain, (![C_44, A_45, B_46]: (k1_funct_1(C_44, '#skF_1'(A_45, B_46, C_44))=A_45 | ~r2_hidden('#skF_1'(A_45, B_46, C_44), k1_relat_1(C_44)) | ~v1_funct_1(C_44) | ~r2_hidden(A_45, k9_relat_1(C_44, B_46)) | ~v1_relat_1(C_44))), inference(resolution, [status(thm)], [c_6, c_48])).
% 2.37/1.41  tff(c_113, plain, (![C_47, A_48, B_49]: (k1_funct_1(C_47, '#skF_1'(A_48, B_49, C_47))=A_48 | ~v1_funct_1(C_47) | ~r2_hidden(A_48, k9_relat_1(C_47, B_49)) | ~v1_relat_1(C_47))), inference(resolution, [status(thm)], [c_8, c_98])).
% 2.37/1.41  tff(c_146, plain, (![B_52, A_53, A_54]: (k1_funct_1(B_52, '#skF_1'(A_53, k2_relat_1(A_54), B_52))=A_53 | ~v1_funct_1(B_52) | ~r2_hidden(A_53, k2_relat_1(k5_relat_1(A_54, B_52))) | ~v1_relat_1(B_52) | ~v1_relat_1(B_52) | ~v1_relat_1(A_54))), inference(superposition, [status(thm), theory('equality')], [c_10, c_113])).
% 2.37/1.41  tff(c_160, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', k2_relat_1('#skF_4'), '#skF_3'))='#skF_2' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_146])).
% 2.37/1.41  tff(c_167, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_2', k2_relat_1('#skF_4'), '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_30, c_160])).
% 2.37/1.41  tff(c_20, plain, (![B_16, A_15]: (r2_hidden(k1_funct_1(B_16, A_15), k2_relat_1(B_16)) | ~r2_hidden(A_15, k1_relat_1(B_16)) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.37/1.41  tff(c_174, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3')) | ~r2_hidden('#skF_1'('#skF_2', k2_relat_1('#skF_4'), '#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_167, c_20])).
% 2.37/1.41  tff(c_180, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3')) | ~r2_hidden('#skF_1'('#skF_2', k2_relat_1('#skF_4'), '#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_174])).
% 2.37/1.41  tff(c_181, plain, (~r2_hidden('#skF_1'('#skF_2', k2_relat_1('#skF_4'), '#skF_3'), k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_22, c_180])).
% 2.37/1.41  tff(c_185, plain, (~r2_hidden('#skF_2', k9_relat_1('#skF_3', k2_relat_1('#skF_4'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_181])).
% 2.37/1.41  tff(c_191, plain, (~r2_hidden('#skF_2', k9_relat_1('#skF_3', k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_185])).
% 2.37/1.41  tff(c_202, plain, (~r2_hidden('#skF_2', k2_relat_1(k5_relat_1('#skF_4', '#skF_3'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10, c_191])).
% 2.37/1.41  tff(c_205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_24, c_202])).
% 2.37/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.41  
% 2.37/1.41  Inference rules
% 2.37/1.41  ----------------------
% 2.37/1.41  #Ref     : 0
% 2.37/1.41  #Sup     : 41
% 2.37/1.41  #Fact    : 0
% 2.37/1.41  #Define  : 0
% 2.37/1.41  #Split   : 0
% 2.37/1.41  #Chain   : 0
% 2.37/1.41  #Close   : 0
% 2.37/1.41  
% 2.37/1.41  Ordering : KBO
% 2.37/1.41  
% 2.37/1.41  Simplification rules
% 2.37/1.41  ----------------------
% 2.37/1.41  #Subsume      : 3
% 2.37/1.41  #Demod        : 15
% 2.37/1.41  #Tautology    : 9
% 2.37/1.41  #SimpNegUnit  : 1
% 2.37/1.41  #BackRed      : 1
% 2.37/1.41  
% 2.37/1.41  #Partial instantiations: 0
% 2.37/1.41  #Strategies tried      : 1
% 2.37/1.41  
% 2.37/1.41  Timing (in seconds)
% 2.37/1.41  ----------------------
% 2.37/1.41  Preprocessing        : 0.36
% 2.37/1.41  Parsing              : 0.20
% 2.37/1.41  CNF conversion       : 0.02
% 2.37/1.41  Main loop            : 0.27
% 2.37/1.41  Inferencing          : 0.12
% 2.37/1.41  Reduction            : 0.07
% 2.37/1.41  Demodulation         : 0.05
% 2.37/1.41  BG Simplification    : 0.02
% 2.37/1.41  Subsumption          : 0.04
% 2.37/1.42  Abstraction          : 0.02
% 2.37/1.42  MUC search           : 0.00
% 2.37/1.42  Cooper               : 0.00
% 2.37/1.42  Total                : 0.67
% 2.37/1.42  Index Insertion      : 0.00
% 2.37/1.42  Index Deletion       : 0.00
% 2.37/1.42  Index Matching       : 0.00
% 2.37/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
