%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:40 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 101 expanded)
%              Number of leaves         :   25 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 ( 124 expanded)
%              Number of equality atoms :   33 (  73 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_68,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_50,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(c_34,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_214,plain,(
    ! [A_45,B_46,C_47] :
      ( ~ r1_xboole_0(A_45,B_46)
      | ~ r2_hidden(C_47,k3_xboole_0(A_45,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_398,plain,(
    ! [A_55,B_56] :
      ( ~ r1_xboole_0(A_55,B_56)
      | v1_xboole_0(k3_xboole_0(A_55,B_56)) ) ),
    inference(resolution,[status(thm)],[c_6,c_214])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_159,plain,(
    ! [B_38,A_39] :
      ( ~ v1_xboole_0(B_38)
      | B_38 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_162,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_8,c_159])).

tff(c_422,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_xboole_0(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_398,c_162])).

tff(c_430,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_422])).

tff(c_459,plain,(
    ! [A_59,B_60] : k2_xboole_0(k3_xboole_0(A_59,B_60),k4_xboole_0(A_59,B_60)) = A_59 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_474,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_459])).

tff(c_72,plain,(
    ! [B_35,A_36] : k2_xboole_0(B_35,A_36) = k2_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_88,plain,(
    ! [A_36] : k2_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_14])).

tff(c_899,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_88])).

tff(c_174,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k2_xboole_0(A_42,B_43)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_193,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_174])).

tff(c_1263,plain,(
    ! [A_86,C_87,B_88] : k2_xboole_0(k4_xboole_0(A_86,C_87),k4_xboole_0(B_88,C_87)) = k4_xboole_0(k2_xboole_0(A_86,B_88),C_87) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1354,plain,(
    ! [A_12,B_88] : k4_xboole_0(k2_xboole_0(A_12,B_88),A_12) = k2_xboole_0(k1_xboole_0,k4_xboole_0(B_88,A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_1263])).

tff(c_1394,plain,(
    ! [A_12,B_88] : k4_xboole_0(k2_xboole_0(A_12,B_88),A_12) = k4_xboole_0(B_88,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1354])).

tff(c_36,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_429,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_422])).

tff(c_477,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_459])).

tff(c_682,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_477])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    k2_xboole_0('#skF_5','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_41,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_40])).

tff(c_2182,plain,(
    ! [A_111,B_112] : k4_xboole_0(k2_xboole_0(A_111,B_112),A_111) = k4_xboole_0(B_112,A_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1354])).

tff(c_2264,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_2182])).

tff(c_2288,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_1394,c_682,c_2264])).

tff(c_2290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_2288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:06:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.57  
% 3.37/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.57  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.37/1.57  
% 3.37/1.57  %Foreground sorts:
% 3.37/1.57  
% 3.37/1.57  
% 3.37/1.57  %Background operators:
% 3.37/1.57  
% 3.37/1.57  
% 3.37/1.57  %Foreground operators:
% 3.37/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.37/1.57  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.37/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.37/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.37/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.37/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.37/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.37/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.37/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.37/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.37/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.37/1.57  
% 3.37/1.59  tff(f_85, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_xboole_1)).
% 3.37/1.59  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.37/1.59  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.37/1.59  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.37/1.59  tff(f_76, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.37/1.59  tff(f_68, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.37/1.59  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.37/1.59  tff(f_50, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.37/1.59  tff(f_64, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.37/1.59  tff(f_62, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 3.37/1.59  tff(c_34, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.37/1.59  tff(c_38, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.37/1.59  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.37/1.59  tff(c_214, plain, (![A_45, B_46, C_47]: (~r1_xboole_0(A_45, B_46) | ~r2_hidden(C_47, k3_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.37/1.59  tff(c_398, plain, (![A_55, B_56]: (~r1_xboole_0(A_55, B_56) | v1_xboole_0(k3_xboole_0(A_55, B_56)))), inference(resolution, [status(thm)], [c_6, c_214])).
% 3.37/1.59  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.37/1.59  tff(c_159, plain, (![B_38, A_39]: (~v1_xboole_0(B_38) | B_38=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.37/1.59  tff(c_162, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_8, c_159])).
% 3.37/1.59  tff(c_422, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_xboole_0(A_57, B_58))), inference(resolution, [status(thm)], [c_398, c_162])).
% 3.37/1.59  tff(c_430, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_422])).
% 3.37/1.59  tff(c_459, plain, (![A_59, B_60]: (k2_xboole_0(k3_xboole_0(A_59, B_60), k4_xboole_0(A_59, B_60))=A_59)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.37/1.59  tff(c_474, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_430, c_459])).
% 3.37/1.59  tff(c_72, plain, (![B_35, A_36]: (k2_xboole_0(B_35, A_36)=k2_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.37/1.59  tff(c_14, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.37/1.59  tff(c_88, plain, (![A_36]: (k2_xboole_0(k1_xboole_0, A_36)=A_36)), inference(superposition, [status(thm), theory('equality')], [c_72, c_14])).
% 3.37/1.59  tff(c_899, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_474, c_88])).
% 3.37/1.59  tff(c_174, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k2_xboole_0(A_42, B_43))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.37/1.59  tff(c_193, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_174])).
% 3.37/1.59  tff(c_1263, plain, (![A_86, C_87, B_88]: (k2_xboole_0(k4_xboole_0(A_86, C_87), k4_xboole_0(B_88, C_87))=k4_xboole_0(k2_xboole_0(A_86, B_88), C_87))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.37/1.59  tff(c_1354, plain, (![A_12, B_88]: (k4_xboole_0(k2_xboole_0(A_12, B_88), A_12)=k2_xboole_0(k1_xboole_0, k4_xboole_0(B_88, A_12)))), inference(superposition, [status(thm), theory('equality')], [c_193, c_1263])).
% 3.37/1.59  tff(c_1394, plain, (![A_12, B_88]: (k4_xboole_0(k2_xboole_0(A_12, B_88), A_12)=k4_xboole_0(B_88, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1354])).
% 3.37/1.59  tff(c_36, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.37/1.59  tff(c_429, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_422])).
% 3.37/1.59  tff(c_477, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_429, c_459])).
% 3.37/1.59  tff(c_682, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_88, c_477])).
% 3.37/1.59  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.37/1.59  tff(c_40, plain, (k2_xboole_0('#skF_5', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.37/1.59  tff(c_41, plain, (k2_xboole_0('#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_40])).
% 3.37/1.59  tff(c_2182, plain, (![A_111, B_112]: (k4_xboole_0(k2_xboole_0(A_111, B_112), A_111)=k4_xboole_0(B_112, A_111))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1354])).
% 3.37/1.59  tff(c_2264, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_41, c_2182])).
% 3.37/1.59  tff(c_2288, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_899, c_1394, c_682, c_2264])).
% 3.37/1.59  tff(c_2290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_2288])).
% 3.37/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.59  
% 3.37/1.59  Inference rules
% 3.37/1.59  ----------------------
% 3.37/1.59  #Ref     : 1
% 3.37/1.59  #Sup     : 583
% 3.37/1.59  #Fact    : 0
% 3.37/1.59  #Define  : 0
% 3.37/1.59  #Split   : 4
% 3.37/1.59  #Chain   : 0
% 3.37/1.59  #Close   : 0
% 3.37/1.59  
% 3.37/1.59  Ordering : KBO
% 3.37/1.59  
% 3.37/1.59  Simplification rules
% 3.37/1.59  ----------------------
% 3.37/1.59  #Subsume      : 58
% 3.37/1.59  #Demod        : 420
% 3.37/1.59  #Tautology    : 359
% 3.37/1.59  #SimpNegUnit  : 10
% 3.37/1.59  #BackRed      : 2
% 3.37/1.59  
% 3.37/1.59  #Partial instantiations: 0
% 3.37/1.59  #Strategies tried      : 1
% 3.37/1.59  
% 3.37/1.59  Timing (in seconds)
% 3.37/1.59  ----------------------
% 3.37/1.59  Preprocessing        : 0.30
% 3.37/1.59  Parsing              : 0.16
% 3.37/1.59  CNF conversion       : 0.02
% 3.37/1.59  Main loop            : 0.54
% 3.37/1.59  Inferencing          : 0.18
% 3.37/1.59  Reduction            : 0.22
% 3.37/1.59  Demodulation         : 0.18
% 3.37/1.59  BG Simplification    : 0.02
% 3.37/1.59  Subsumption          : 0.08
% 3.37/1.59  Abstraction          : 0.02
% 3.37/1.59  MUC search           : 0.00
% 3.37/1.59  Cooper               : 0.00
% 3.37/1.59  Total                : 0.87
% 3.37/1.59  Index Insertion      : 0.00
% 3.37/1.59  Index Deletion       : 0.00
% 3.37/1.59  Index Matching       : 0.00
% 3.37/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
