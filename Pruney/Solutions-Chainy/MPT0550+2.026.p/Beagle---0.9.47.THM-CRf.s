%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:55 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 107 expanded)
%              Number of leaves         :   26 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 207 expanded)
%              Number of equality atoms :   29 (  76 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( r1_xboole_0(k1_relat_1(B_18),A_17)
      | k7_relat_1(B_18,A_17) != k1_xboole_0
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_103,plain,(
    ! [B_39,A_40] :
      ( k1_relat_1(k7_relat_1(B_39,A_40)) = A_40
      | ~ r1_tarski(A_40,k1_relat_1(B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_106,plain,
    ( k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_103])).

tff(c_109,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_106])).

tff(c_78,plain,(
    ! [B_33,A_34] :
      ( k3_xboole_0(k1_relat_1(B_33),A_34) = k1_relat_1(k7_relat_1(B_33,A_34))
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_160,plain,(
    ! [B_47,A_48,C_49] :
      ( ~ r1_xboole_0(k1_relat_1(B_47),A_48)
      | ~ r2_hidden(C_49,k1_relat_1(k7_relat_1(B_47,A_48)))
      | ~ v1_relat_1(B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_4])).

tff(c_163,plain,(
    ! [C_49] :
      ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_49,'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_160])).

tff(c_169,plain,(
    ! [C_49] :
      ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_49,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_163])).

tff(c_185,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_188,plain,
    ( k7_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_185])).

tff(c_191,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_188])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_119,plain,(
    ! [A_17] :
      ( r1_xboole_0('#skF_3',A_17)
      | k7_relat_1(k7_relat_1('#skF_4','#skF_3'),A_17) != k1_xboole_0
      | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_22])).

tff(c_192,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_195,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_192])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_195])).

tff(c_201,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_12,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) != k1_xboole_0
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_207,plain,
    ( k2_relat_1(k7_relat_1('#skF_4','#skF_3')) != k1_xboole_0
    | k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_201,c_12])).

tff(c_213,plain,(
    k2_relat_1(k7_relat_1('#skF_4','#skF_3')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_207])).

tff(c_216,plain,
    ( k9_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_213])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_216])).

tff(c_222,plain,(
    ! [C_52] : ~ r2_hidden(C_52,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_226,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_222])).

tff(c_230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:37:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.36  
% 2.06/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.06/1.37  
% 2.06/1.37  %Foreground sorts:
% 2.06/1.37  
% 2.06/1.37  
% 2.06/1.37  %Background operators:
% 2.06/1.37  
% 2.06/1.37  
% 2.06/1.37  %Foreground operators:
% 2.06/1.37  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.06/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.06/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.06/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.06/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.06/1.37  
% 2.06/1.38  tff(f_90, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 2.06/1.38  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.06/1.38  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.06/1.38  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.06/1.38  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 2.06/1.38  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.06/1.38  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.06/1.38  tff(f_51, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.06/1.38  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.06/1.38  tff(c_28, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.06/1.38  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.06/1.38  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.06/1.38  tff(c_24, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.06/1.38  tff(c_10, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.06/1.38  tff(c_22, plain, (![B_18, A_17]: (r1_xboole_0(k1_relat_1(B_18), A_17) | k7_relat_1(B_18, A_17)!=k1_xboole_0 | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.06/1.38  tff(c_26, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.06/1.38  tff(c_103, plain, (![B_39, A_40]: (k1_relat_1(k7_relat_1(B_39, A_40))=A_40 | ~r1_tarski(A_40, k1_relat_1(B_39)) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.06/1.38  tff(c_106, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))='#skF_3' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_103])).
% 2.06/1.38  tff(c_109, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_106])).
% 2.06/1.38  tff(c_78, plain, (![B_33, A_34]: (k3_xboole_0(k1_relat_1(B_33), A_34)=k1_relat_1(k7_relat_1(B_33, A_34)) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.06/1.38  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.38  tff(c_160, plain, (![B_47, A_48, C_49]: (~r1_xboole_0(k1_relat_1(B_47), A_48) | ~r2_hidden(C_49, k1_relat_1(k7_relat_1(B_47, A_48))) | ~v1_relat_1(B_47))), inference(superposition, [status(thm), theory('equality')], [c_78, c_4])).
% 2.06/1.38  tff(c_163, plain, (![C_49]: (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | ~r2_hidden(C_49, '#skF_3') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_109, c_160])).
% 2.06/1.38  tff(c_169, plain, (![C_49]: (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | ~r2_hidden(C_49, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_163])).
% 2.06/1.38  tff(c_185, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_169])).
% 2.06/1.38  tff(c_188, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_185])).
% 2.06/1.38  tff(c_191, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_188])).
% 2.06/1.38  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.06/1.38  tff(c_119, plain, (![A_17]: (r1_xboole_0('#skF_3', A_17) | k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), A_17)!=k1_xboole_0 | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_109, c_22])).
% 2.06/1.38  tff(c_192, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_119])).
% 2.06/1.38  tff(c_195, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_192])).
% 2.06/1.38  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_195])).
% 2.06/1.38  tff(c_201, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_119])).
% 2.06/1.38  tff(c_12, plain, (![A_12]: (k2_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.06/1.38  tff(c_207, plain, (k2_relat_1(k7_relat_1('#skF_4', '#skF_3'))!=k1_xboole_0 | k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_201, c_12])).
% 2.06/1.38  tff(c_213, plain, (k2_relat_1(k7_relat_1('#skF_4', '#skF_3'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_191, c_207])).
% 2.06/1.38  tff(c_216, plain, (k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10, c_213])).
% 2.06/1.38  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_216])).
% 2.06/1.38  tff(c_222, plain, (![C_52]: (~r2_hidden(C_52, '#skF_3'))), inference(splitRight, [status(thm)], [c_169])).
% 2.06/1.38  tff(c_226, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_222])).
% 2.06/1.38  tff(c_230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_226])).
% 2.06/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.38  
% 2.06/1.38  Inference rules
% 2.06/1.38  ----------------------
% 2.06/1.38  #Ref     : 0
% 2.06/1.38  #Sup     : 43
% 2.06/1.38  #Fact    : 0
% 2.06/1.38  #Define  : 0
% 2.06/1.38  #Split   : 4
% 2.06/1.38  #Chain   : 0
% 2.06/1.38  #Close   : 0
% 2.06/1.38  
% 2.06/1.38  Ordering : KBO
% 2.06/1.38  
% 2.06/1.38  Simplification rules
% 2.06/1.38  ----------------------
% 2.06/1.38  #Subsume      : 3
% 2.06/1.38  #Demod        : 10
% 2.06/1.38  #Tautology    : 13
% 2.06/1.38  #SimpNegUnit  : 3
% 2.06/1.38  #BackRed      : 0
% 2.06/1.38  
% 2.06/1.38  #Partial instantiations: 0
% 2.06/1.38  #Strategies tried      : 1
% 2.06/1.38  
% 2.06/1.38  Timing (in seconds)
% 2.06/1.38  ----------------------
% 2.06/1.38  Preprocessing        : 0.36
% 2.06/1.38  Parsing              : 0.18
% 2.06/1.38  CNF conversion       : 0.03
% 2.06/1.38  Main loop            : 0.20
% 2.06/1.38  Inferencing          : 0.08
% 2.06/1.38  Reduction            : 0.06
% 2.06/1.38  Demodulation         : 0.04
% 2.06/1.38  BG Simplification    : 0.02
% 2.06/1.38  Subsumption          : 0.03
% 2.06/1.38  Abstraction          : 0.01
% 2.06/1.38  MUC search           : 0.00
% 2.06/1.38  Cooper               : 0.00
% 2.06/1.38  Total                : 0.60
% 2.06/1.38  Index Insertion      : 0.00
% 2.06/1.38  Index Deletion       : 0.00
% 2.06/1.38  Index Matching       : 0.00
% 2.06/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
