%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:13 EST 2020

% Result     : Theorem 5.26s
% Output     : CNFRefutation 5.62s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 185 expanded)
%              Number of leaves         :   23 (  78 expanded)
%              Depth                    :   13
%              Number of atoms          :  120 ( 539 expanded)
%              Number of equality atoms :   26 ( 136 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,B)
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

tff(f_58,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(c_40,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_44,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    ! [A_11,B_14] :
      ( k1_funct_1(A_11,B_14) = k1_xboole_0
      | r2_hidden(B_14,k1_relat_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( k3_xboole_0(k1_relat_1(B_10),A_9) = k1_relat_1(k7_relat_1(B_10,A_9))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_160,plain,(
    ! [D_37,A_38,B_39] :
      ( r2_hidden(D_37,k3_xboole_0(A_38,B_39))
      | ~ r2_hidden(D_37,B_39)
      | ~ r2_hidden(D_37,A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_172,plain,(
    ! [D_37,B_10,A_9] :
      ( r2_hidden(D_37,k1_relat_1(k7_relat_1(B_10,A_9)))
      | ~ r2_hidden(D_37,A_9)
      | ~ r2_hidden(D_37,k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_160])).

tff(c_488,plain,(
    ! [C_71,B_72,A_73] :
      ( k1_funct_1(k7_relat_1(C_71,B_72),A_73) = k1_funct_1(C_71,A_73)
      | ~ r2_hidden(A_73,k1_relat_1(k7_relat_1(C_71,B_72)))
      | ~ v1_funct_1(C_71)
      | ~ v1_relat_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2998,plain,(
    ! [B_202,A_203,D_204] :
      ( k1_funct_1(k7_relat_1(B_202,A_203),D_204) = k1_funct_1(B_202,D_204)
      | ~ v1_funct_1(B_202)
      | ~ r2_hidden(D_204,A_203)
      | ~ r2_hidden(D_204,k1_relat_1(B_202))
      | ~ v1_relat_1(B_202) ) ),
    inference(resolution,[status(thm)],[c_172,c_488])).

tff(c_3199,plain,(
    ! [A_205,A_206,B_207] :
      ( k1_funct_1(k7_relat_1(A_205,A_206),B_207) = k1_funct_1(A_205,B_207)
      | ~ r2_hidden(B_207,A_206)
      | k1_funct_1(A_205,B_207) = k1_xboole_0
      | ~ v1_funct_1(A_205)
      | ~ v1_relat_1(A_205) ) ),
    inference(resolution,[status(thm)],[c_30,c_2998])).

tff(c_38,plain,(
    k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3211,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | k1_funct_1('#skF_5','#skF_3') = k1_xboole_0
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3199,c_38])).

tff(c_3221,plain,(
    k1_funct_1('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_3211])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( v1_funct_1(k7_relat_1(A_16,B_17))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_34,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k7_relat_1(A_16,B_17))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_94,plain,(
    ! [B_33,A_34] :
      ( k3_xboole_0(k1_relat_1(B_33),A_34) = k1_relat_1(k7_relat_1(B_33,A_34))
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_188,plain,(
    ! [D_45,B_46,A_47] :
      ( r2_hidden(D_45,k1_relat_1(B_46))
      | ~ r2_hidden(D_45,k1_relat_1(k7_relat_1(B_46,A_47)))
      | ~ v1_relat_1(B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_8])).

tff(c_3399,plain,(
    ! [B_214,B_215,A_216] :
      ( r2_hidden(B_214,k1_relat_1(B_215))
      | ~ v1_relat_1(B_215)
      | k1_funct_1(k7_relat_1(B_215,A_216),B_214) = k1_xboole_0
      | ~ v1_funct_1(k7_relat_1(B_215,A_216))
      | ~ v1_relat_1(k7_relat_1(B_215,A_216)) ) ),
    inference(resolution,[status(thm)],[c_30,c_188])).

tff(c_3403,plain,(
    ! [B_217,A_218,B_219] :
      ( r2_hidden(B_217,k1_relat_1(A_218))
      | k1_funct_1(k7_relat_1(A_218,B_219),B_217) = k1_xboole_0
      | ~ v1_funct_1(k7_relat_1(A_218,B_219))
      | ~ v1_funct_1(A_218)
      | ~ v1_relat_1(A_218) ) ),
    inference(resolution,[status(thm)],[c_34,c_3399])).

tff(c_3407,plain,(
    ! [B_220,A_221,B_222] :
      ( r2_hidden(B_220,k1_relat_1(A_221))
      | k1_funct_1(k7_relat_1(A_221,B_222),B_220) = k1_xboole_0
      | ~ v1_funct_1(A_221)
      | ~ v1_relat_1(A_221) ) ),
    inference(resolution,[status(thm)],[c_32,c_3403])).

tff(c_26,plain,(
    ! [B_14,A_11] :
      ( r2_hidden(k4_tarski(B_14,k1_funct_1(A_11,B_14)),A_11)
      | ~ r2_hidden(B_14,k1_relat_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3227,plain,
    ( r2_hidden(k4_tarski('#skF_3',k1_xboole_0),'#skF_5')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3221,c_26])).

tff(c_3231,plain,
    ( r2_hidden(k4_tarski('#skF_3',k1_xboole_0),'#skF_5')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3227])).

tff(c_3349,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_3231])).

tff(c_3410,plain,(
    ! [B_222] :
      ( k1_funct_1(k7_relat_1('#skF_5',B_222),'#skF_3') = k1_xboole_0
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3407,c_3349])).

tff(c_3488,plain,(
    ! [B_222] : k1_funct_1(k7_relat_1('#skF_5',B_222),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3410])).

tff(c_3223,plain,(
    k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3221,c_38])).

tff(c_3504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3488,c_3223])).

tff(c_3506,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3231])).

tff(c_534,plain,(
    ! [B_10,A_9,D_37] :
      ( k1_funct_1(k7_relat_1(B_10,A_9),D_37) = k1_funct_1(B_10,D_37)
      | ~ v1_funct_1(B_10)
      | ~ r2_hidden(D_37,A_9)
      | ~ r2_hidden(D_37,k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_172,c_488])).

tff(c_3508,plain,(
    ! [A_9] :
      ( k1_funct_1(k7_relat_1('#skF_5',A_9),'#skF_3') = k1_funct_1('#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ r2_hidden('#skF_3',A_9)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3506,c_534])).

tff(c_3626,plain,(
    ! [A_227] :
      ( k1_funct_1(k7_relat_1('#skF_5',A_227),'#skF_3') = k1_xboole_0
      | ~ r2_hidden('#skF_3',A_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3221,c_3508])).

tff(c_3632,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3626,c_3223])).

tff(c_3657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3632])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:29:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.26/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.26/2.07  
% 5.26/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.62/2.07  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 5.62/2.07  
% 5.62/2.07  %Foreground sorts:
% 5.62/2.07  
% 5.62/2.07  
% 5.62/2.07  %Background operators:
% 5.62/2.07  
% 5.62/2.07  
% 5.62/2.07  %Foreground operators:
% 5.62/2.07  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.62/2.07  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.62/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.62/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.62/2.07  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.62/2.07  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.62/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.62/2.07  tff('#skF_5', type, '#skF_5': $i).
% 5.62/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.62/2.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.62/2.07  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.62/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.62/2.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.62/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.62/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.62/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.62/2.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.62/2.07  
% 5.62/2.08  tff(f_83, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, B) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 5.62/2.08  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 5.62/2.08  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 5.62/2.08  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.62/2.08  tff(f_74, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_funct_1)).
% 5.62/2.08  tff(f_66, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 5.62/2.08  tff(c_40, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.62/2.08  tff(c_44, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.62/2.08  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.62/2.08  tff(c_30, plain, (![A_11, B_14]: (k1_funct_1(A_11, B_14)=k1_xboole_0 | r2_hidden(B_14, k1_relat_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.62/2.08  tff(c_22, plain, (![B_10, A_9]: (k3_xboole_0(k1_relat_1(B_10), A_9)=k1_relat_1(k7_relat_1(B_10, A_9)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.62/2.08  tff(c_160, plain, (![D_37, A_38, B_39]: (r2_hidden(D_37, k3_xboole_0(A_38, B_39)) | ~r2_hidden(D_37, B_39) | ~r2_hidden(D_37, A_38))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.62/2.08  tff(c_172, plain, (![D_37, B_10, A_9]: (r2_hidden(D_37, k1_relat_1(k7_relat_1(B_10, A_9))) | ~r2_hidden(D_37, A_9) | ~r2_hidden(D_37, k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(superposition, [status(thm), theory('equality')], [c_22, c_160])).
% 5.62/2.08  tff(c_488, plain, (![C_71, B_72, A_73]: (k1_funct_1(k7_relat_1(C_71, B_72), A_73)=k1_funct_1(C_71, A_73) | ~r2_hidden(A_73, k1_relat_1(k7_relat_1(C_71, B_72))) | ~v1_funct_1(C_71) | ~v1_relat_1(C_71))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.62/2.08  tff(c_2998, plain, (![B_202, A_203, D_204]: (k1_funct_1(k7_relat_1(B_202, A_203), D_204)=k1_funct_1(B_202, D_204) | ~v1_funct_1(B_202) | ~r2_hidden(D_204, A_203) | ~r2_hidden(D_204, k1_relat_1(B_202)) | ~v1_relat_1(B_202))), inference(resolution, [status(thm)], [c_172, c_488])).
% 5.62/2.08  tff(c_3199, plain, (![A_205, A_206, B_207]: (k1_funct_1(k7_relat_1(A_205, A_206), B_207)=k1_funct_1(A_205, B_207) | ~r2_hidden(B_207, A_206) | k1_funct_1(A_205, B_207)=k1_xboole_0 | ~v1_funct_1(A_205) | ~v1_relat_1(A_205))), inference(resolution, [status(thm)], [c_30, c_2998])).
% 5.62/2.08  tff(c_38, plain, (k1_funct_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.62/2.08  tff(c_3211, plain, (~r2_hidden('#skF_3', '#skF_4') | k1_funct_1('#skF_5', '#skF_3')=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3199, c_38])).
% 5.62/2.08  tff(c_3221, plain, (k1_funct_1('#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_3211])).
% 5.62/2.08  tff(c_32, plain, (![A_16, B_17]: (v1_funct_1(k7_relat_1(A_16, B_17)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.62/2.08  tff(c_34, plain, (![A_16, B_17]: (v1_relat_1(k7_relat_1(A_16, B_17)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.62/2.08  tff(c_94, plain, (![B_33, A_34]: (k3_xboole_0(k1_relat_1(B_33), A_34)=k1_relat_1(k7_relat_1(B_33, A_34)) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.62/2.08  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.62/2.08  tff(c_188, plain, (![D_45, B_46, A_47]: (r2_hidden(D_45, k1_relat_1(B_46)) | ~r2_hidden(D_45, k1_relat_1(k7_relat_1(B_46, A_47))) | ~v1_relat_1(B_46))), inference(superposition, [status(thm), theory('equality')], [c_94, c_8])).
% 5.62/2.08  tff(c_3399, plain, (![B_214, B_215, A_216]: (r2_hidden(B_214, k1_relat_1(B_215)) | ~v1_relat_1(B_215) | k1_funct_1(k7_relat_1(B_215, A_216), B_214)=k1_xboole_0 | ~v1_funct_1(k7_relat_1(B_215, A_216)) | ~v1_relat_1(k7_relat_1(B_215, A_216)))), inference(resolution, [status(thm)], [c_30, c_188])).
% 5.62/2.08  tff(c_3403, plain, (![B_217, A_218, B_219]: (r2_hidden(B_217, k1_relat_1(A_218)) | k1_funct_1(k7_relat_1(A_218, B_219), B_217)=k1_xboole_0 | ~v1_funct_1(k7_relat_1(A_218, B_219)) | ~v1_funct_1(A_218) | ~v1_relat_1(A_218))), inference(resolution, [status(thm)], [c_34, c_3399])).
% 5.62/2.08  tff(c_3407, plain, (![B_220, A_221, B_222]: (r2_hidden(B_220, k1_relat_1(A_221)) | k1_funct_1(k7_relat_1(A_221, B_222), B_220)=k1_xboole_0 | ~v1_funct_1(A_221) | ~v1_relat_1(A_221))), inference(resolution, [status(thm)], [c_32, c_3403])).
% 5.62/2.08  tff(c_26, plain, (![B_14, A_11]: (r2_hidden(k4_tarski(B_14, k1_funct_1(A_11, B_14)), A_11) | ~r2_hidden(B_14, k1_relat_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.62/2.08  tff(c_3227, plain, (r2_hidden(k4_tarski('#skF_3', k1_xboole_0), '#skF_5') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3221, c_26])).
% 5.62/2.08  tff(c_3231, plain, (r2_hidden(k4_tarski('#skF_3', k1_xboole_0), '#skF_5') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3227])).
% 5.62/2.08  tff(c_3349, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_3231])).
% 5.62/2.08  tff(c_3410, plain, (![B_222]: (k1_funct_1(k7_relat_1('#skF_5', B_222), '#skF_3')=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_3407, c_3349])).
% 5.62/2.08  tff(c_3488, plain, (![B_222]: (k1_funct_1(k7_relat_1('#skF_5', B_222), '#skF_3')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3410])).
% 5.62/2.08  tff(c_3223, plain, (k1_funct_1(k7_relat_1('#skF_5', '#skF_4'), '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3221, c_38])).
% 5.62/2.08  tff(c_3504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3488, c_3223])).
% 5.62/2.08  tff(c_3506, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_3231])).
% 5.62/2.08  tff(c_534, plain, (![B_10, A_9, D_37]: (k1_funct_1(k7_relat_1(B_10, A_9), D_37)=k1_funct_1(B_10, D_37) | ~v1_funct_1(B_10) | ~r2_hidden(D_37, A_9) | ~r2_hidden(D_37, k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_172, c_488])).
% 5.62/2.08  tff(c_3508, plain, (![A_9]: (k1_funct_1(k7_relat_1('#skF_5', A_9), '#skF_3')=k1_funct_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~r2_hidden('#skF_3', A_9) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_3506, c_534])).
% 5.62/2.08  tff(c_3626, plain, (![A_227]: (k1_funct_1(k7_relat_1('#skF_5', A_227), '#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_3', A_227))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3221, c_3508])).
% 5.62/2.08  tff(c_3632, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3626, c_3223])).
% 5.62/2.08  tff(c_3657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_3632])).
% 5.62/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.62/2.08  
% 5.62/2.08  Inference rules
% 5.62/2.08  ----------------------
% 5.62/2.08  #Ref     : 0
% 5.62/2.08  #Sup     : 892
% 5.62/2.08  #Fact    : 0
% 5.62/2.08  #Define  : 0
% 5.62/2.08  #Split   : 1
% 5.62/2.08  #Chain   : 0
% 5.62/2.08  #Close   : 0
% 5.62/2.08  
% 5.62/2.08  Ordering : KBO
% 5.62/2.08  
% 5.62/2.08  Simplification rules
% 5.62/2.08  ----------------------
% 5.62/2.08  #Subsume      : 196
% 5.62/2.08  #Demod        : 192
% 5.62/2.08  #Tautology    : 64
% 5.62/2.08  #SimpNegUnit  : 0
% 5.62/2.08  #BackRed      : 2
% 5.62/2.08  
% 5.62/2.08  #Partial instantiations: 0
% 5.62/2.08  #Strategies tried      : 1
% 5.62/2.08  
% 5.62/2.08  Timing (in seconds)
% 5.62/2.08  ----------------------
% 5.70/2.09  Preprocessing        : 0.32
% 5.70/2.09  Parsing              : 0.16
% 5.70/2.09  CNF conversion       : 0.02
% 5.70/2.09  Main loop            : 1.00
% 5.70/2.09  Inferencing          : 0.32
% 5.70/2.09  Reduction            : 0.31
% 5.70/2.09  Demodulation         : 0.25
% 5.70/2.09  BG Simplification    : 0.05
% 5.70/2.09  Subsumption          : 0.24
% 5.70/2.09  Abstraction          : 0.07
% 5.70/2.09  MUC search           : 0.00
% 5.70/2.09  Cooper               : 0.00
% 5.70/2.09  Total                : 1.35
% 5.70/2.09  Index Insertion      : 0.00
% 5.70/2.09  Index Deletion       : 0.00
% 5.70/2.09  Index Matching       : 0.00
% 5.70/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
