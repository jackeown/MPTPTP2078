%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:44 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   56 (  70 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 104 expanded)
%              Number of equality atoms :   23 (  34 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_xboole_0(k2_relat_1(A),k1_relat_1(B))
           => k5_relat_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_44,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(c_28,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_72,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_89,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_34])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_92,plain,(
    r1_xboole_0('#skF_1',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_89,c_2])).

tff(c_10,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_12] : k2_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_139,plain,(
    ! [A_34,B_35] :
      ( k5_relat_1(A_34,B_35) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_34),k1_relat_1(B_35))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_145,plain,(
    ! [A_12,B_35] :
      ( k5_relat_1(k6_relat_1(A_12),B_35) = k1_xboole_0
      | ~ r1_xboole_0(A_12,k1_relat_1(B_35))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_139])).

tff(c_163,plain,(
    ! [A_36,B_37] :
      ( k5_relat_1(k6_relat_1(A_36),B_37) = k1_xboole_0
      | ~ r1_xboole_0(A_36,k1_relat_1(B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_145])).

tff(c_169,plain,
    ( k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_163])).

tff(c_182,plain,(
    k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_169])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( k5_relat_1(k6_relat_1(A_15),B_16) = k7_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_191,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_24])).

tff(c_198,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_191])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_198])).

tff(c_201,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [B_21,A_22] :
      ( r1_xboole_0(B_21,A_22)
      | ~ r1_xboole_0(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_66,plain,(
    ! [A_3] : r1_xboole_0(k1_xboole_0,A_3) ),
    inference(resolution,[status(thm)],[c_4,c_63])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_202,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_234,plain,(
    ! [B_44,A_45] :
      ( k3_xboole_0(k1_relat_1(B_44),A_45) = k1_relat_1(k7_relat_1(B_44,A_45))
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( ~ r1_xboole_0(k3_xboole_0(A_4,B_5),B_5)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_512,plain,(
    ! [B_62,A_63] :
      ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(B_62,A_63)),A_63)
      | r1_xboole_0(k1_relat_1(B_62),A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_6])).

tff(c_530,plain,
    ( ~ r1_xboole_0(k1_relat_1(k1_xboole_0),'#skF_1')
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_512])).

tff(c_546,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_66,c_14,c_530])).

tff(c_548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_546])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:57:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.65  
% 2.83/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.65  %$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.83/1.65  
% 2.83/1.65  %Foreground sorts:
% 2.83/1.65  
% 2.83/1.65  
% 2.83/1.65  %Background operators:
% 2.83/1.65  
% 2.83/1.65  
% 2.83/1.65  %Foreground operators:
% 2.83/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.65  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.83/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.65  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.83/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.83/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.83/1.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.83/1.65  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.65  tff('#skF_1', type, '#skF_1': $i).
% 2.83/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.65  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.83/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.83/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.65  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.83/1.65  
% 2.83/1.67  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.83/1.67  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.83/1.67  tff(f_41, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.83/1.67  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.83/1.67  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k1_relat_1(B)) => (k5_relat_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_relat_1)).
% 2.83/1.67  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.83/1.67  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.83/1.67  tff(f_44, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.83/1.67  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.83/1.67  tff(f_37, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 2.83/1.67  tff(c_28, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.83/1.67  tff(c_72, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_28])).
% 2.83/1.67  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.83/1.67  tff(c_34, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.83/1.67  tff(c_89, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_72, c_34])).
% 2.83/1.67  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.67  tff(c_92, plain, (r1_xboole_0('#skF_1', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_89, c_2])).
% 2.83/1.67  tff(c_10, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.83/1.67  tff(c_20, plain, (![A_12]: (k2_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.83/1.67  tff(c_139, plain, (![A_34, B_35]: (k5_relat_1(A_34, B_35)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_34), k1_relat_1(B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.83/1.67  tff(c_145, plain, (![A_12, B_35]: (k5_relat_1(k6_relat_1(A_12), B_35)=k1_xboole_0 | ~r1_xboole_0(A_12, k1_relat_1(B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_139])).
% 2.83/1.67  tff(c_163, plain, (![A_36, B_37]: (k5_relat_1(k6_relat_1(A_36), B_37)=k1_xboole_0 | ~r1_xboole_0(A_36, k1_relat_1(B_37)) | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_145])).
% 2.83/1.67  tff(c_169, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_92, c_163])).
% 2.83/1.67  tff(c_182, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_169])).
% 2.83/1.67  tff(c_24, plain, (![A_15, B_16]: (k5_relat_1(k6_relat_1(A_15), B_16)=k7_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.83/1.67  tff(c_191, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_182, c_24])).
% 2.83/1.67  tff(c_198, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_191])).
% 2.83/1.67  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_198])).
% 2.83/1.67  tff(c_201, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 2.83/1.67  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.67  tff(c_63, plain, (![B_21, A_22]: (r1_xboole_0(B_21, A_22) | ~r1_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.67  tff(c_66, plain, (![A_3]: (r1_xboole_0(k1_xboole_0, A_3))), inference(resolution, [status(thm)], [c_4, c_63])).
% 2.83/1.67  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.83/1.67  tff(c_202, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 2.83/1.67  tff(c_234, plain, (![B_44, A_45]: (k3_xboole_0(k1_relat_1(B_44), A_45)=k1_relat_1(k7_relat_1(B_44, A_45)) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.83/1.67  tff(c_6, plain, (![A_4, B_5]: (~r1_xboole_0(k3_xboole_0(A_4, B_5), B_5) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.83/1.67  tff(c_512, plain, (![B_62, A_63]: (~r1_xboole_0(k1_relat_1(k7_relat_1(B_62, A_63)), A_63) | r1_xboole_0(k1_relat_1(B_62), A_63) | ~v1_relat_1(B_62))), inference(superposition, [status(thm), theory('equality')], [c_234, c_6])).
% 2.83/1.67  tff(c_530, plain, (~r1_xboole_0(k1_relat_1(k1_xboole_0), '#skF_1') | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_202, c_512])).
% 2.83/1.67  tff(c_546, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_66, c_14, c_530])).
% 2.83/1.67  tff(c_548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_546])).
% 2.83/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.67  
% 2.83/1.67  Inference rules
% 2.83/1.67  ----------------------
% 2.83/1.67  #Ref     : 0
% 2.83/1.67  #Sup     : 115
% 2.83/1.67  #Fact    : 0
% 2.83/1.67  #Define  : 0
% 2.83/1.67  #Split   : 3
% 2.83/1.67  #Chain   : 0
% 2.83/1.67  #Close   : 0
% 2.83/1.67  
% 2.83/1.67  Ordering : KBO
% 2.83/1.67  
% 2.83/1.67  Simplification rules
% 2.83/1.67  ----------------------
% 2.83/1.67  #Subsume      : 10
% 2.83/1.67  #Demod        : 70
% 2.83/1.67  #Tautology    : 67
% 2.83/1.67  #SimpNegUnit  : 4
% 2.83/1.67  #BackRed      : 0
% 2.83/1.67  
% 2.83/1.67  #Partial instantiations: 0
% 2.83/1.67  #Strategies tried      : 1
% 2.83/1.67  
% 2.83/1.67  Timing (in seconds)
% 2.83/1.67  ----------------------
% 2.83/1.68  Preprocessing        : 0.48
% 2.83/1.68  Parsing              : 0.26
% 2.83/1.68  CNF conversion       : 0.03
% 2.83/1.68  Main loop            : 0.39
% 2.83/1.68  Inferencing          : 0.15
% 2.83/1.68  Reduction            : 0.12
% 2.83/1.68  Demodulation         : 0.09
% 2.83/1.68  BG Simplification    : 0.02
% 2.83/1.68  Subsumption          : 0.06
% 2.83/1.68  Abstraction          : 0.02
% 2.83/1.68  MUC search           : 0.00
% 2.83/1.68  Cooper               : 0.00
% 2.83/1.68  Total                : 0.92
% 2.83/1.68  Index Insertion      : 0.00
% 2.83/1.68  Index Deletion       : 0.00
% 2.83/1.68  Index Matching       : 0.00
% 2.83/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
