%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:51 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   53 (  96 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 163 expanded)
%              Number of equality atoms :   30 (  67 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_44,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_144,plain,(
    ! [B_25,A_26] :
      ( r1_xboole_0(k1_relat_1(B_25),A_26)
      | k7_relat_1(B_25,A_26) != k1_xboole_0
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_61,plain,(
    k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_10,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_62,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_26])).

tff(c_84,plain,(
    ! [B_17,A_18] :
      ( k7_relat_1(B_17,A_18) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_17),A_18)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_87,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_84])).

tff(c_93,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_87])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_97,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_8])).

tff(c_107,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_10,c_97])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_107])).

tff(c_110,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_150,plain,
    ( k7_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_144,c_110])).

tff(c_157,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_150])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_111,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_127,plain,(
    ! [B_21,A_22] :
      ( k2_relat_1(k7_relat_1(B_21,A_22)) = k9_relat_1(B_21,A_22)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_3] :
      ( k8_relat_1(k2_relat_1(A_3),A_3) = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_158,plain,(
    ! [B_27,A_28] :
      ( k8_relat_1(k9_relat_1(B_27,A_28),k7_relat_1(B_27,A_28)) = k7_relat_1(B_27,A_28)
      | ~ v1_relat_1(k7_relat_1(B_27,A_28))
      | ~ v1_relat_1(B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_4])).

tff(c_167,plain,
    ( k8_relat_1(k1_xboole_0,k7_relat_1('#skF_2','#skF_1')) = k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_158])).

tff(c_171,plain,
    ( k8_relat_1(k1_xboole_0,k7_relat_1('#skF_2','#skF_1')) = k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_167])).

tff(c_172,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_175,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_172])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_175])).

tff(c_181,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_6,plain,(
    ! [A_4] :
      ( k8_relat_1(k1_xboole_0,A_4) = k1_xboole_0
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_185,plain,(
    k8_relat_1(k1_xboole_0,k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_181,c_6])).

tff(c_180,plain,(
    k8_relat_1(k1_xboole_0,k7_relat_1('#skF_2','#skF_1')) = k7_relat_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_202,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_180])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:33:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.20  
% 1.91/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.20  %$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.99/1.20  
% 1.99/1.20  %Foreground sorts:
% 1.99/1.20  
% 1.99/1.20  
% 1.99/1.20  %Background operators:
% 1.99/1.20  
% 1.99/1.20  
% 1.99/1.20  %Foreground operators:
% 1.99/1.20  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.99/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.99/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.99/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.20  
% 1.99/1.22  tff(f_57, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 1.99/1.22  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 1.99/1.22  tff(f_44, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.99/1.22  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.99/1.22  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.99/1.22  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 1.99/1.22  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 1.99/1.22  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.99/1.22  tff(c_144, plain, (![B_25, A_26]: (r1_xboole_0(k1_relat_1(B_25), A_26) | k7_relat_1(B_25, A_26)!=k1_xboole_0 | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.99/1.22  tff(c_20, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.99/1.22  tff(c_61, plain, (k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_20])).
% 1.99/1.22  tff(c_10, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.99/1.22  tff(c_26, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.99/1.22  tff(c_62, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_61, c_26])).
% 1.99/1.22  tff(c_84, plain, (![B_17, A_18]: (k7_relat_1(B_17, A_18)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_17), A_18) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.99/1.22  tff(c_87, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_84])).
% 1.99/1.22  tff(c_93, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_87])).
% 1.99/1.22  tff(c_8, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.22  tff(c_97, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_93, c_8])).
% 1.99/1.22  tff(c_107, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_10, c_97])).
% 1.99/1.22  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_107])).
% 1.99/1.22  tff(c_110, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_20])).
% 1.99/1.22  tff(c_150, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_144, c_110])).
% 1.99/1.22  tff(c_157, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_150])).
% 1.99/1.22  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.22  tff(c_111, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_20])).
% 1.99/1.22  tff(c_127, plain, (![B_21, A_22]: (k2_relat_1(k7_relat_1(B_21, A_22))=k9_relat_1(B_21, A_22) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.22  tff(c_4, plain, (![A_3]: (k8_relat_1(k2_relat_1(A_3), A_3)=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.22  tff(c_158, plain, (![B_27, A_28]: (k8_relat_1(k9_relat_1(B_27, A_28), k7_relat_1(B_27, A_28))=k7_relat_1(B_27, A_28) | ~v1_relat_1(k7_relat_1(B_27, A_28)) | ~v1_relat_1(B_27))), inference(superposition, [status(thm), theory('equality')], [c_127, c_4])).
% 1.99/1.22  tff(c_167, plain, (k8_relat_1(k1_xboole_0, k7_relat_1('#skF_2', '#skF_1'))=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_111, c_158])).
% 1.99/1.22  tff(c_171, plain, (k8_relat_1(k1_xboole_0, k7_relat_1('#skF_2', '#skF_1'))=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_167])).
% 1.99/1.22  tff(c_172, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_171])).
% 1.99/1.22  tff(c_175, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_172])).
% 1.99/1.22  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_175])).
% 1.99/1.22  tff(c_181, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_171])).
% 1.99/1.22  tff(c_6, plain, (![A_4]: (k8_relat_1(k1_xboole_0, A_4)=k1_xboole_0 | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.22  tff(c_185, plain, (k8_relat_1(k1_xboole_0, k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0), inference(resolution, [status(thm)], [c_181, c_6])).
% 1.99/1.22  tff(c_180, plain, (k8_relat_1(k1_xboole_0, k7_relat_1('#skF_2', '#skF_1'))=k7_relat_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_171])).
% 1.99/1.22  tff(c_202, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_185, c_180])).
% 1.99/1.22  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_202])).
% 1.99/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.22  
% 1.99/1.22  Inference rules
% 1.99/1.22  ----------------------
% 1.99/1.22  #Ref     : 0
% 1.99/1.22  #Sup     : 43
% 1.99/1.22  #Fact    : 0
% 1.99/1.22  #Define  : 0
% 1.99/1.22  #Split   : 3
% 1.99/1.22  #Chain   : 0
% 1.99/1.22  #Close   : 0
% 1.99/1.22  
% 1.99/1.22  Ordering : KBO
% 1.99/1.22  
% 1.99/1.22  Simplification rules
% 1.99/1.22  ----------------------
% 1.99/1.22  #Subsume      : 2
% 1.99/1.22  #Demod        : 10
% 1.99/1.22  #Tautology    : 29
% 1.99/1.22  #SimpNegUnit  : 4
% 1.99/1.22  #BackRed      : 0
% 1.99/1.22  
% 1.99/1.22  #Partial instantiations: 0
% 1.99/1.22  #Strategies tried      : 1
% 1.99/1.22  
% 1.99/1.22  Timing (in seconds)
% 1.99/1.22  ----------------------
% 1.99/1.22  Preprocessing        : 0.28
% 1.99/1.22  Parsing              : 0.16
% 1.99/1.22  CNF conversion       : 0.02
% 1.99/1.22  Main loop            : 0.17
% 1.99/1.22  Inferencing          : 0.07
% 1.99/1.22  Reduction            : 0.04
% 1.99/1.22  Demodulation         : 0.03
% 1.99/1.22  BG Simplification    : 0.01
% 1.99/1.22  Subsumption          : 0.03
% 1.99/1.22  Abstraction          : 0.01
% 1.99/1.22  MUC search           : 0.00
% 1.99/1.22  Cooper               : 0.00
% 1.99/1.22  Total                : 0.48
% 1.99/1.22  Index Insertion      : 0.00
% 1.99/1.22  Index Deletion       : 0.00
% 1.99/1.22  Index Matching       : 0.00
% 1.99/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
