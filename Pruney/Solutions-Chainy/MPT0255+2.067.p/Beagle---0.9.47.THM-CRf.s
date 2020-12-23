%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:48 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 341 expanded)
%              Number of leaves         :   29 ( 125 expanded)
%              Depth                    :   14
%              Number of atoms          :   75 ( 499 expanded)
%              Number of equality atoms :   38 ( 165 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_36,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_46,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_144,plain,(
    ! [B_43,A_44] :
      ( ~ v1_xboole_0(k2_xboole_0(B_43,A_44))
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_147,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_144])).

tff(c_155,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_147])).

tff(c_134,plain,(
    ! [B_40,A_41] :
      ( ~ v1_xboole_0(B_40)
      | B_40 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_137,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_4,c_134])).

tff(c_173,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_155,c_137])).

tff(c_8,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_179,plain,(
    ! [A_5] : r1_tarski('#skF_5',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_112,plain,(
    k2_xboole_0('#skF_5',k2_tarski('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_187,plain,(
    k2_xboole_0('#skF_5',k2_tarski('#skF_3','#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_112])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( ~ v1_xboole_0(k2_xboole_0(B_4,A_3))
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_191,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0(k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_6])).

tff(c_195,plain,(
    v1_xboole_0(k2_tarski('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_191])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | B_7 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_174,plain,(
    ! [A_6] :
      ( A_6 = '#skF_5'
      | ~ v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_155,c_10])).

tff(c_208,plain,(
    k2_tarski('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_195,c_174])).

tff(c_323,plain,(
    ! [A_61,C_62,B_63] :
      ( r2_hidden(A_61,C_62)
      | ~ r1_tarski(k2_tarski(A_61,B_63),C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_326,plain,(
    ! [C_62] :
      ( r2_hidden('#skF_3',C_62)
      | ~ r1_tarski('#skF_5',C_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_323])).

tff(c_331,plain,(
    ! [C_62] : r2_hidden('#skF_3',C_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_326])).

tff(c_381,plain,(
    ! [D_73,B_74,A_75] :
      ( D_73 = B_74
      | D_73 = A_75
      | ~ r2_hidden(D_73,k2_tarski(A_75,B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_402,plain,(
    ! [B_74,A_75] :
      ( B_74 = '#skF_3'
      | A_75 = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_331,c_381])).

tff(c_421,plain,(
    ! [A_75] : A_75 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_402])).

tff(c_422,plain,(
    ! [A_77] : A_77 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_402])).

tff(c_30,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_156,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_334,plain,(
    ! [A_65] : k3_tarski(k1_tarski(A_65)) = k2_xboole_0(A_65,A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_156])).

tff(c_68,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),B_26) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_84,plain,(
    ! [B_36,A_25] : k2_xboole_0(B_36,k1_tarski(A_25)) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_44])).

tff(c_176,plain,(
    ! [B_36,A_25] : k2_xboole_0(B_36,k1_tarski(A_25)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_84])).

tff(c_347,plain,(
    ! [A_25] : k3_tarski(k1_tarski(k1_tarski(A_25))) != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_176])).

tff(c_441,plain,(
    '#skF_5' != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_347])).

tff(c_617,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_441])).

tff(c_618,plain,(
    ! [B_74] : B_74 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_402])).

tff(c_619,plain,(
    ! [B_1442] : B_1442 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_402])).

tff(c_178,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),B_26) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_44])).

tff(c_675,plain,(
    '#skF_5' != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_178])).

tff(c_835,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_618,c_675])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:04:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.36  
% 2.52/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.36  %$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.52/1.36  
% 2.52/1.36  %Foreground sorts:
% 2.52/1.36  
% 2.52/1.36  
% 2.52/1.36  %Background operators:
% 2.52/1.36  
% 2.52/1.36  
% 2.52/1.36  %Foreground operators:
% 2.52/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.52/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.52/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.52/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.52/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.52/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.52/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.52/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.52/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.52/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.52/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.52/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.52/1.36  
% 2.76/1.37  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.76/1.37  tff(f_74, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.76/1.37  tff(f_34, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.76/1.37  tff(f_44, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.76/1.37  tff(f_36, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.76/1.37  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.76/1.37  tff(f_67, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.76/1.37  tff(f_53, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.76/1.37  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.76/1.37  tff(f_61, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.76/1.37  tff(f_70, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.76/1.37  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.76/1.37  tff(c_46, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.76/1.37  tff(c_144, plain, (![B_43, A_44]: (~v1_xboole_0(k2_xboole_0(B_43, A_44)) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.76/1.37  tff(c_147, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_46, c_144])).
% 2.76/1.37  tff(c_155, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_147])).
% 2.76/1.37  tff(c_134, plain, (![B_40, A_41]: (~v1_xboole_0(B_40) | B_40=A_41 | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.37  tff(c_137, plain, (![A_41]: (k1_xboole_0=A_41 | ~v1_xboole_0(A_41))), inference(resolution, [status(thm)], [c_4, c_134])).
% 2.76/1.37  tff(c_173, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_155, c_137])).
% 2.76/1.37  tff(c_8, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.76/1.37  tff(c_179, plain, (![A_5]: (r1_tarski('#skF_5', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_8])).
% 2.76/1.37  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.76/1.37  tff(c_112, plain, (k2_xboole_0('#skF_5', k2_tarski('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_46, c_2])).
% 2.76/1.37  tff(c_187, plain, (k2_xboole_0('#skF_5', k2_tarski('#skF_3', '#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_112])).
% 2.76/1.37  tff(c_6, plain, (![B_4, A_3]: (~v1_xboole_0(k2_xboole_0(B_4, A_3)) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.76/1.37  tff(c_191, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0(k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_187, c_6])).
% 2.76/1.37  tff(c_195, plain, (v1_xboole_0(k2_tarski('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_191])).
% 2.76/1.37  tff(c_10, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | B_7=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.76/1.37  tff(c_174, plain, (![A_6]: (A_6='#skF_5' | ~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_155, c_10])).
% 2.76/1.37  tff(c_208, plain, (k2_tarski('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_195, c_174])).
% 2.76/1.37  tff(c_323, plain, (![A_61, C_62, B_63]: (r2_hidden(A_61, C_62) | ~r1_tarski(k2_tarski(A_61, B_63), C_62))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.37  tff(c_326, plain, (![C_62]: (r2_hidden('#skF_3', C_62) | ~r1_tarski('#skF_5', C_62))), inference(superposition, [status(thm), theory('equality')], [c_208, c_323])).
% 2.76/1.37  tff(c_331, plain, (![C_62]: (r2_hidden('#skF_3', C_62))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_326])).
% 2.76/1.37  tff(c_381, plain, (![D_73, B_74, A_75]: (D_73=B_74 | D_73=A_75 | ~r2_hidden(D_73, k2_tarski(A_75, B_74)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.76/1.37  tff(c_402, plain, (![B_74, A_75]: (B_74='#skF_3' | A_75='#skF_3')), inference(resolution, [status(thm)], [c_331, c_381])).
% 2.76/1.37  tff(c_421, plain, (![A_75]: (A_75='#skF_3')), inference(splitLeft, [status(thm)], [c_402])).
% 2.76/1.37  tff(c_422, plain, (![A_77]: (A_77='#skF_3')), inference(splitLeft, [status(thm)], [c_402])).
% 2.76/1.37  tff(c_30, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.76/1.37  tff(c_156, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.76/1.37  tff(c_334, plain, (![A_65]: (k3_tarski(k1_tarski(A_65))=k2_xboole_0(A_65, A_65))), inference(superposition, [status(thm), theory('equality')], [c_30, c_156])).
% 2.76/1.37  tff(c_68, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.76/1.37  tff(c_44, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.76/1.37  tff(c_84, plain, (![B_36, A_25]: (k2_xboole_0(B_36, k1_tarski(A_25))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_68, c_44])).
% 2.76/1.37  tff(c_176, plain, (![B_36, A_25]: (k2_xboole_0(B_36, k1_tarski(A_25))!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_84])).
% 2.76/1.37  tff(c_347, plain, (![A_25]: (k3_tarski(k1_tarski(k1_tarski(A_25)))!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_334, c_176])).
% 2.76/1.37  tff(c_441, plain, ('#skF_5'!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_422, c_347])).
% 2.76/1.37  tff(c_617, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_421, c_441])).
% 2.76/1.37  tff(c_618, plain, (![B_74]: (B_74='#skF_3')), inference(splitRight, [status(thm)], [c_402])).
% 2.76/1.37  tff(c_619, plain, (![B_1442]: (B_1442='#skF_3')), inference(splitRight, [status(thm)], [c_402])).
% 2.76/1.37  tff(c_178, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), B_26)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_44])).
% 2.76/1.37  tff(c_675, plain, ('#skF_5'!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_619, c_178])).
% 2.76/1.37  tff(c_835, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_618, c_675])).
% 2.76/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.37  
% 2.76/1.37  Inference rules
% 2.76/1.37  ----------------------
% 2.76/1.37  #Ref     : 0
% 2.76/1.37  #Sup     : 280
% 2.76/1.37  #Fact    : 0
% 2.76/1.37  #Define  : 0
% 2.76/1.37  #Split   : 2
% 2.76/1.37  #Chain   : 0
% 2.76/1.37  #Close   : 0
% 2.76/1.37  
% 2.76/1.37  Ordering : KBO
% 2.76/1.37  
% 2.76/1.37  Simplification rules
% 2.76/1.37  ----------------------
% 2.76/1.37  #Subsume      : 77
% 2.76/1.37  #Demod        : 48
% 2.76/1.37  #Tautology    : 59
% 2.76/1.37  #SimpNegUnit  : 0
% 2.76/1.37  #BackRed      : 8
% 2.76/1.37  
% 2.76/1.37  #Partial instantiations: 71
% 2.76/1.37  #Strategies tried      : 1
% 2.76/1.37  
% 2.76/1.37  Timing (in seconds)
% 2.76/1.37  ----------------------
% 2.76/1.38  Preprocessing        : 0.30
% 2.76/1.38  Parsing              : 0.16
% 2.76/1.38  CNF conversion       : 0.02
% 2.76/1.38  Main loop            : 0.33
% 2.76/1.38  Inferencing          : 0.13
% 2.76/1.38  Reduction            : 0.11
% 2.76/1.38  Demodulation         : 0.08
% 2.76/1.38  BG Simplification    : 0.02
% 2.76/1.38  Subsumption          : 0.05
% 2.76/1.38  Abstraction          : 0.02
% 2.76/1.38  MUC search           : 0.00
% 2.76/1.38  Cooper               : 0.00
% 2.76/1.38  Total                : 0.66
% 2.76/1.38  Index Insertion      : 0.00
% 2.76/1.38  Index Deletion       : 0.00
% 2.76/1.38  Index Matching       : 0.00
% 2.76/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
