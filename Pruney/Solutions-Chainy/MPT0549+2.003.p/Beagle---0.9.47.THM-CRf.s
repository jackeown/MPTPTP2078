%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:48 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   54 (  78 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 126 expanded)
%              Number of equality atoms :   40 (  59 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_94,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_22,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_122,plain,(
    k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_22])).

tff(c_144,plain,(
    ! [B_28,A_29] :
      ( k3_xboole_0(k1_relat_1(B_28),A_29) = k1_relat_1(k7_relat_1(B_28,A_29))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_94,c_4])).

tff(c_150,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_98])).

tff(c_173,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_150])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_124,plain,(
    ! [A_25] :
      ( k2_relat_1(A_25) = k1_xboole_0
      | k1_relat_1(A_25) != k1_xboole_0
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_348,plain,(
    ! [A_36,B_37] :
      ( k2_relat_1(k7_relat_1(A_36,B_37)) = k1_xboole_0
      | k1_relat_1(k7_relat_1(A_36,B_37)) != k1_xboole_0
      | ~ v1_relat_1(A_36) ) ),
    inference(resolution,[status(thm)],[c_10,c_124])).

tff(c_587,plain,(
    ! [B_46,A_47] :
      ( k9_relat_1(B_46,A_47) = k1_xboole_0
      | k1_relat_1(k7_relat_1(B_46,A_47)) != k1_xboole_0
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_348])).

tff(c_593,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_587])).

tff(c_598,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_593])).

tff(c_600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_598])).

tff(c_601,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_84,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) = k1_xboole_0
      | k2_relat_1(A_24) != k1_xboole_0
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_755,plain,(
    ! [A_59,B_60] :
      ( k1_relat_1(k7_relat_1(A_59,B_60)) = k1_xboole_0
      | k2_relat_1(k7_relat_1(A_59,B_60)) != k1_xboole_0
      | ~ v1_relat_1(A_59) ) ),
    inference(resolution,[status(thm)],[c_10,c_84])).

tff(c_952,plain,(
    ! [B_71,A_72] :
      ( k1_relat_1(k7_relat_1(B_71,A_72)) = k1_xboole_0
      | k9_relat_1(B_71,A_72) != k1_xboole_0
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_755])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_634,plain,(
    ! [B_51,A_52] :
      ( k3_xboole_0(k1_relat_1(B_51),A_52) = k1_relat_1(k7_relat_1(B_51,A_52))
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_679,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,k1_relat_1(B_56)) = k1_relat_1(k7_relat_1(B_56,A_55))
      | ~ v1_relat_1(B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_634])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_602,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_609,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_602])).

tff(c_611,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_609])).

tff(c_692,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_679,c_611])).

tff(c_716,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_692])).

tff(c_961,plain,
    ( k9_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_716])).

tff(c_976,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_601,c_961])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:00:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.42  
% 2.76/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.42  %$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.76/1.42  
% 2.76/1.42  %Foreground sorts:
% 2.76/1.42  
% 2.76/1.42  
% 2.76/1.42  %Background operators:
% 2.76/1.42  
% 2.76/1.42  
% 2.76/1.42  %Foreground operators:
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.76/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.76/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.76/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.76/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.76/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.42  
% 2.76/1.43  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 2.76/1.43  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.76/1.43  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.76/1.43  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.76/1.43  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.76/1.43  tff(f_47, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.76/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.76/1.43  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.76/1.43  tff(c_28, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.76/1.43  tff(c_94, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 2.76/1.43  tff(c_22, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.76/1.43  tff(c_122, plain, (k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_94, c_22])).
% 2.76/1.43  tff(c_144, plain, (![B_28, A_29]: (k3_xboole_0(k1_relat_1(B_28), A_29)=k1_relat_1(k7_relat_1(B_28, A_29)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.76/1.43  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.76/1.43  tff(c_98, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_94, c_4])).
% 2.76/1.43  tff(c_150, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_144, c_98])).
% 2.76/1.43  tff(c_173, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_150])).
% 2.76/1.43  tff(c_12, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.76/1.43  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.76/1.43  tff(c_124, plain, (![A_25]: (k2_relat_1(A_25)=k1_xboole_0 | k1_relat_1(A_25)!=k1_xboole_0 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.76/1.43  tff(c_348, plain, (![A_36, B_37]: (k2_relat_1(k7_relat_1(A_36, B_37))=k1_xboole_0 | k1_relat_1(k7_relat_1(A_36, B_37))!=k1_xboole_0 | ~v1_relat_1(A_36))), inference(resolution, [status(thm)], [c_10, c_124])).
% 2.76/1.43  tff(c_587, plain, (![B_46, A_47]: (k9_relat_1(B_46, A_47)=k1_xboole_0 | k1_relat_1(k7_relat_1(B_46, A_47))!=k1_xboole_0 | ~v1_relat_1(B_46) | ~v1_relat_1(B_46))), inference(superposition, [status(thm), theory('equality')], [c_12, c_348])).
% 2.76/1.43  tff(c_593, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_173, c_587])).
% 2.76/1.43  tff(c_598, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_593])).
% 2.76/1.43  tff(c_600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_598])).
% 2.76/1.43  tff(c_601, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 2.76/1.43  tff(c_84, plain, (![A_24]: (k1_relat_1(A_24)=k1_xboole_0 | k2_relat_1(A_24)!=k1_xboole_0 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.76/1.43  tff(c_755, plain, (![A_59, B_60]: (k1_relat_1(k7_relat_1(A_59, B_60))=k1_xboole_0 | k2_relat_1(k7_relat_1(A_59, B_60))!=k1_xboole_0 | ~v1_relat_1(A_59))), inference(resolution, [status(thm)], [c_10, c_84])).
% 2.76/1.43  tff(c_952, plain, (![B_71, A_72]: (k1_relat_1(k7_relat_1(B_71, A_72))=k1_xboole_0 | k9_relat_1(B_71, A_72)!=k1_xboole_0 | ~v1_relat_1(B_71) | ~v1_relat_1(B_71))), inference(superposition, [status(thm), theory('equality')], [c_12, c_755])).
% 2.76/1.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.76/1.43  tff(c_634, plain, (![B_51, A_52]: (k3_xboole_0(k1_relat_1(B_51), A_52)=k1_relat_1(k7_relat_1(B_51, A_52)) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.76/1.43  tff(c_679, plain, (![A_55, B_56]: (k3_xboole_0(A_55, k1_relat_1(B_56))=k1_relat_1(k7_relat_1(B_56, A_55)) | ~v1_relat_1(B_56))), inference(superposition, [status(thm), theory('equality')], [c_2, c_634])).
% 2.76/1.43  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.76/1.43  tff(c_602, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 2.76/1.43  tff(c_609, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_602])).
% 2.76/1.43  tff(c_611, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_609])).
% 2.76/1.43  tff(c_692, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_679, c_611])).
% 2.76/1.43  tff(c_716, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_692])).
% 2.76/1.43  tff(c_961, plain, (k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_952, c_716])).
% 2.76/1.43  tff(c_976, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_601, c_961])).
% 2.76/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.43  
% 2.76/1.43  Inference rules
% 2.76/1.43  ----------------------
% 2.76/1.43  #Ref     : 0
% 2.76/1.43  #Sup     : 246
% 2.76/1.43  #Fact    : 0
% 2.76/1.43  #Define  : 0
% 2.76/1.43  #Split   : 2
% 2.76/1.43  #Chain   : 0
% 2.76/1.43  #Close   : 0
% 2.76/1.43  
% 2.76/1.43  Ordering : KBO
% 2.76/1.43  
% 2.76/1.43  Simplification rules
% 2.76/1.43  ----------------------
% 2.76/1.43  #Subsume      : 22
% 2.76/1.43  #Demod        : 92
% 2.76/1.43  #Tautology    : 117
% 2.76/1.43  #SimpNegUnit  : 3
% 2.76/1.43  #BackRed      : 0
% 2.76/1.43  
% 2.76/1.43  #Partial instantiations: 0
% 2.76/1.43  #Strategies tried      : 1
% 2.76/1.43  
% 2.76/1.43  Timing (in seconds)
% 2.76/1.43  ----------------------
% 2.76/1.44  Preprocessing        : 0.29
% 2.76/1.44  Parsing              : 0.15
% 2.76/1.44  CNF conversion       : 0.02
% 2.76/1.44  Main loop            : 0.39
% 2.76/1.44  Inferencing          : 0.14
% 2.76/1.44  Reduction            : 0.14
% 2.76/1.44  Demodulation         : 0.12
% 2.76/1.44  BG Simplification    : 0.02
% 2.76/1.44  Subsumption          : 0.06
% 2.76/1.44  Abstraction          : 0.03
% 2.76/1.44  MUC search           : 0.00
% 2.76/1.44  Cooper               : 0.00
% 2.76/1.44  Total                : 0.71
% 2.76/1.44  Index Insertion      : 0.00
% 2.76/1.44  Index Deletion       : 0.00
% 2.76/1.44  Index Matching       : 0.00
% 2.76/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
