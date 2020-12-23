%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:34 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   54 (  87 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 186 expanded)
%              Number of equality atoms :    3 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    ! [A_15,B_17] :
      ( r1_tarski(k2_relat_1(A_15),k2_relat_1(B_17))
      | ~ r1_tarski(A_15,B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_41,plain,(
    ! [A_32] :
      ( k2_xboole_0(k1_relat_1(A_32),k2_relat_1(A_32)) = k3_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,k2_xboole_0(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_47,plain,(
    ! [A_6,A_32] :
      ( r1_tarski(A_6,k3_relat_1(A_32))
      | ~ r1_tarski(A_6,k2_relat_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_8])).

tff(c_18,plain,(
    ! [A_15,B_17] :
      ( r1_tarski(k1_relat_1(A_15),k1_relat_1(B_17))
      | ~ r1_tarski(A_15,B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_14] :
      ( k2_xboole_0(k1_relat_1(A_14),k2_relat_1(A_14)) = k3_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,(
    ! [C_29,B_30,A_31] :
      ( r2_hidden(C_29,B_30)
      | ~ r2_hidden(C_29,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,(
    ! [A_41,B_42,B_43] :
      ( r2_hidden('#skF_1'(A_41,B_42),B_43)
      | ~ r1_tarski(A_41,B_43)
      | r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_6,c_37])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_99,plain,(
    ! [A_48,B_49,B_50,B_51] :
      ( r2_hidden('#skF_1'(A_48,B_49),B_50)
      | ~ r1_tarski(B_51,B_50)
      | ~ r1_tarski(A_48,B_51)
      | r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_69,c_2])).

tff(c_139,plain,(
    ! [A_54,B_55,A_56,B_57] :
      ( r2_hidden('#skF_1'(A_54,B_55),k2_xboole_0(A_56,B_57))
      | ~ r1_tarski(A_54,A_56)
      | r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_10,c_99])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_168,plain,(
    ! [A_59,A_60,B_61] :
      ( ~ r1_tarski(A_59,A_60)
      | r1_tarski(A_59,k2_xboole_0(A_60,B_61)) ) ),
    inference(resolution,[status(thm)],[c_139,c_4])).

tff(c_175,plain,(
    ! [A_62,A_63] :
      ( ~ r1_tarski(A_62,k1_relat_1(A_63))
      | r1_tarski(A_62,k3_relat_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_168])).

tff(c_64,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(k2_xboole_0(A_36,C_37),B_38)
      | ~ r1_tarski(C_37,B_38)
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_79,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k3_relat_1(A_46),B_47)
      | ~ r1_tarski(k2_relat_1(A_46),B_47)
      | ~ r1_tarski(k1_relat_1(A_46),B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_64])).

tff(c_20,plain,(
    ~ r1_tarski(k3_relat_1('#skF_2'),k3_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_85,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),k3_relat_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1('#skF_2'),k3_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_79,c_20])).

tff(c_91,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),k3_relat_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1('#skF_2'),k3_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_85])).

tff(c_92,plain,(
    ~ r1_tarski(k1_relat_1('#skF_2'),k3_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_180,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_175,c_92])).

tff(c_187,plain,(
    ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_180])).

tff(c_199,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_187])).

tff(c_203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_199])).

tff(c_204,plain,(
    ~ r1_tarski(k2_relat_1('#skF_2'),k3_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_208,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_47,c_204])).

tff(c_211,plain,(
    ~ r1_tarski(k2_relat_1('#skF_2'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_208])).

tff(c_214,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_211])).

tff(c_218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.22  
% 1.93/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.22  %$ r2_hidden > r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.93/1.22  
% 1.93/1.22  %Foreground sorts:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Background operators:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Foreground operators:
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.22  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.93/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.93/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.22  
% 1.93/1.23  tff(f_69, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 1.93/1.23  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 1.93/1.23  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.93/1.23  tff(f_36, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.93/1.23  tff(f_38, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.93/1.23  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.93/1.23  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.93/1.23  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.93/1.23  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.93/1.23  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.93/1.23  tff(c_16, plain, (![A_15, B_17]: (r1_tarski(k2_relat_1(A_15), k2_relat_1(B_17)) | ~r1_tarski(A_15, B_17) | ~v1_relat_1(B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.93/1.23  tff(c_41, plain, (![A_32]: (k2_xboole_0(k1_relat_1(A_32), k2_relat_1(A_32))=k3_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.93/1.23  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, k2_xboole_0(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.93/1.23  tff(c_47, plain, (![A_6, A_32]: (r1_tarski(A_6, k3_relat_1(A_32)) | ~r1_tarski(A_6, k2_relat_1(A_32)) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_41, c_8])).
% 1.93/1.23  tff(c_18, plain, (![A_15, B_17]: (r1_tarski(k1_relat_1(A_15), k1_relat_1(B_17)) | ~r1_tarski(A_15, B_17) | ~v1_relat_1(B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.93/1.23  tff(c_14, plain, (![A_14]: (k2_xboole_0(k1_relat_1(A_14), k2_relat_1(A_14))=k3_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.93/1.23  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.93/1.23  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.93/1.23  tff(c_37, plain, (![C_29, B_30, A_31]: (r2_hidden(C_29, B_30) | ~r2_hidden(C_29, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.93/1.23  tff(c_69, plain, (![A_41, B_42, B_43]: (r2_hidden('#skF_1'(A_41, B_42), B_43) | ~r1_tarski(A_41, B_43) | r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_6, c_37])).
% 1.93/1.23  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.93/1.23  tff(c_99, plain, (![A_48, B_49, B_50, B_51]: (r2_hidden('#skF_1'(A_48, B_49), B_50) | ~r1_tarski(B_51, B_50) | ~r1_tarski(A_48, B_51) | r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_69, c_2])).
% 1.93/1.23  tff(c_139, plain, (![A_54, B_55, A_56, B_57]: (r2_hidden('#skF_1'(A_54, B_55), k2_xboole_0(A_56, B_57)) | ~r1_tarski(A_54, A_56) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_10, c_99])).
% 1.93/1.23  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.93/1.23  tff(c_168, plain, (![A_59, A_60, B_61]: (~r1_tarski(A_59, A_60) | r1_tarski(A_59, k2_xboole_0(A_60, B_61)))), inference(resolution, [status(thm)], [c_139, c_4])).
% 1.93/1.23  tff(c_175, plain, (![A_62, A_63]: (~r1_tarski(A_62, k1_relat_1(A_63)) | r1_tarski(A_62, k3_relat_1(A_63)) | ~v1_relat_1(A_63))), inference(superposition, [status(thm), theory('equality')], [c_14, c_168])).
% 1.93/1.23  tff(c_64, plain, (![A_36, C_37, B_38]: (r1_tarski(k2_xboole_0(A_36, C_37), B_38) | ~r1_tarski(C_37, B_38) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.93/1.23  tff(c_79, plain, (![A_46, B_47]: (r1_tarski(k3_relat_1(A_46), B_47) | ~r1_tarski(k2_relat_1(A_46), B_47) | ~r1_tarski(k1_relat_1(A_46), B_47) | ~v1_relat_1(A_46))), inference(superposition, [status(thm), theory('equality')], [c_14, c_64])).
% 1.93/1.23  tff(c_20, plain, (~r1_tarski(k3_relat_1('#skF_2'), k3_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.93/1.23  tff(c_85, plain, (~r1_tarski(k2_relat_1('#skF_2'), k3_relat_1('#skF_3')) | ~r1_tarski(k1_relat_1('#skF_2'), k3_relat_1('#skF_3')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_79, c_20])).
% 1.93/1.23  tff(c_91, plain, (~r1_tarski(k2_relat_1('#skF_2'), k3_relat_1('#skF_3')) | ~r1_tarski(k1_relat_1('#skF_2'), k3_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_85])).
% 1.93/1.23  tff(c_92, plain, (~r1_tarski(k1_relat_1('#skF_2'), k3_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_91])).
% 1.93/1.23  tff(c_180, plain, (~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_175, c_92])).
% 1.93/1.23  tff(c_187, plain, (~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_180])).
% 1.93/1.23  tff(c_199, plain, (~r1_tarski('#skF_2', '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_187])).
% 1.93/1.23  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_199])).
% 1.93/1.23  tff(c_204, plain, (~r1_tarski(k2_relat_1('#skF_2'), k3_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_91])).
% 1.93/1.23  tff(c_208, plain, (~r1_tarski(k2_relat_1('#skF_2'), k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_47, c_204])).
% 1.93/1.23  tff(c_211, plain, (~r1_tarski(k2_relat_1('#skF_2'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_208])).
% 1.93/1.23  tff(c_214, plain, (~r1_tarski('#skF_2', '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_211])).
% 1.93/1.23  tff(c_218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_214])).
% 1.93/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  Inference rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Ref     : 0
% 1.93/1.23  #Sup     : 40
% 1.93/1.23  #Fact    : 0
% 1.93/1.23  #Define  : 0
% 1.93/1.23  #Split   : 1
% 1.93/1.23  #Chain   : 0
% 1.93/1.23  #Close   : 0
% 1.93/1.23  
% 1.93/1.23  Ordering : KBO
% 1.93/1.23  
% 1.93/1.23  Simplification rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Subsume      : 2
% 1.93/1.23  #Demod        : 15
% 1.93/1.23  #Tautology    : 4
% 1.93/1.23  #SimpNegUnit  : 0
% 1.93/1.23  #BackRed      : 0
% 1.93/1.23  
% 1.93/1.23  #Partial instantiations: 0
% 1.93/1.23  #Strategies tried      : 1
% 1.93/1.23  
% 1.93/1.23  Timing (in seconds)
% 1.93/1.23  ----------------------
% 2.16/1.24  Preprocessing        : 0.26
% 2.16/1.24  Parsing              : 0.15
% 2.16/1.24  CNF conversion       : 0.02
% 2.16/1.24  Main loop            : 0.21
% 2.16/1.24  Inferencing          : 0.09
% 2.16/1.24  Reduction            : 0.05
% 2.16/1.24  Demodulation         : 0.04
% 2.16/1.24  BG Simplification    : 0.01
% 2.16/1.24  Subsumption          : 0.05
% 2.16/1.24  Abstraction          : 0.01
% 2.16/1.24  MUC search           : 0.00
% 2.16/1.24  Cooper               : 0.00
% 2.16/1.24  Total                : 0.51
% 2.16/1.24  Index Insertion      : 0.00
% 2.16/1.24  Index Deletion       : 0.00
% 2.16/1.24  Index Matching       : 0.00
% 2.16/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
