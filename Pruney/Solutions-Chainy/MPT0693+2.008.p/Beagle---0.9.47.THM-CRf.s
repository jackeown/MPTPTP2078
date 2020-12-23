%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:52 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   46 (  58 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   54 (  84 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_38,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [B_41,A_40] :
      ( k10_relat_1(B_41,k3_xboole_0(k2_relat_1(B_41),A_40)) = k10_relat_1(B_41,A_40)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_555,plain,(
    ! [B_99,A_100] :
      ( k9_relat_1(B_99,k10_relat_1(B_99,A_100)) = A_100
      | ~ r1_tarski(A_100,k2_relat_1(B_99))
      | ~ v1_funct_1(B_99)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1716,plain,(
    ! [B_134,B_135] :
      ( k9_relat_1(B_134,k10_relat_1(B_134,k3_xboole_0(k2_relat_1(B_134),B_135))) = k3_xboole_0(k2_relat_1(B_134),B_135)
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134) ) ),
    inference(resolution,[status(thm)],[c_10,c_555])).

tff(c_2171,plain,(
    ! [B_144,A_145] :
      ( k9_relat_1(B_144,k10_relat_1(B_144,A_145)) = k3_xboole_0(k2_relat_1(B_144),A_145)
      | ~ v1_funct_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_relat_1(B_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1716])).

tff(c_32,plain,(
    ! [A_42] :
      ( k10_relat_1(A_42,k2_relat_1(A_42)) = k1_relat_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1371,plain,(
    ! [B_126] :
      ( k9_relat_1(B_126,k10_relat_1(B_126,k2_relat_1(B_126))) = k2_relat_1(B_126)
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(resolution,[status(thm)],[c_8,c_555])).

tff(c_1573,plain,(
    ! [A_131] :
      ( k9_relat_1(A_131,k1_relat_1(A_131)) = k2_relat_1(A_131)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1371])).

tff(c_36,plain,(
    k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k1_relat_1('#skF_2'))) != k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1579,plain,
    ( k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != k3_xboole_0('#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1573,c_36])).

tff(c_1585,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != k3_xboole_0('#skF_1',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_38,c_1579])).

tff(c_2181,plain,
    ( k3_xboole_0(k2_relat_1('#skF_2'),'#skF_1') != k3_xboole_0('#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2171,c_1585])).

tff(c_2208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_38,c_2,c_2181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.60  
% 3.56/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.60  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.56/1.60  
% 3.56/1.60  %Foreground sorts:
% 3.56/1.60  
% 3.56/1.60  
% 3.56/1.60  %Background operators:
% 3.56/1.60  
% 3.56/1.60  
% 3.56/1.60  %Foreground operators:
% 3.56/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.56/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.56/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.56/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.56/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.56/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.56/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.56/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.60  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.56/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.56/1.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.56/1.60  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.56/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.60  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.56/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.56/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.56/1.60  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.56/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.56/1.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.56/1.60  
% 3.56/1.61  tff(f_76, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 3.56/1.61  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.56/1.61  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 3.56/1.61  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.56/1.61  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 3.56/1.61  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.56/1.61  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.56/1.61  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.56/1.61  tff(c_38, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.56/1.61  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.56/1.61  tff(c_30, plain, (![B_41, A_40]: (k10_relat_1(B_41, k3_xboole_0(k2_relat_1(B_41), A_40))=k10_relat_1(B_41, A_40) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.56/1.61  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.56/1.61  tff(c_555, plain, (![B_99, A_100]: (k9_relat_1(B_99, k10_relat_1(B_99, A_100))=A_100 | ~r1_tarski(A_100, k2_relat_1(B_99)) | ~v1_funct_1(B_99) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.56/1.61  tff(c_1716, plain, (![B_134, B_135]: (k9_relat_1(B_134, k10_relat_1(B_134, k3_xboole_0(k2_relat_1(B_134), B_135)))=k3_xboole_0(k2_relat_1(B_134), B_135) | ~v1_funct_1(B_134) | ~v1_relat_1(B_134))), inference(resolution, [status(thm)], [c_10, c_555])).
% 3.56/1.61  tff(c_2171, plain, (![B_144, A_145]: (k9_relat_1(B_144, k10_relat_1(B_144, A_145))=k3_xboole_0(k2_relat_1(B_144), A_145) | ~v1_funct_1(B_144) | ~v1_relat_1(B_144) | ~v1_relat_1(B_144))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1716])).
% 3.56/1.61  tff(c_32, plain, (![A_42]: (k10_relat_1(A_42, k2_relat_1(A_42))=k1_relat_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.56/1.61  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.56/1.61  tff(c_1371, plain, (![B_126]: (k9_relat_1(B_126, k10_relat_1(B_126, k2_relat_1(B_126)))=k2_relat_1(B_126) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126))), inference(resolution, [status(thm)], [c_8, c_555])).
% 3.56/1.61  tff(c_1573, plain, (![A_131]: (k9_relat_1(A_131, k1_relat_1(A_131))=k2_relat_1(A_131) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131) | ~v1_relat_1(A_131))), inference(superposition, [status(thm), theory('equality')], [c_32, c_1371])).
% 3.56/1.61  tff(c_36, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k1_relat_1('#skF_2')))!=k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.56/1.61  tff(c_1579, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1573, c_36])).
% 3.56/1.61  tff(c_1585, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_38, c_1579])).
% 3.56/1.61  tff(c_2181, plain, (k3_xboole_0(k2_relat_1('#skF_2'), '#skF_1')!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2171, c_1585])).
% 3.56/1.61  tff(c_2208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_38, c_2, c_2181])).
% 3.56/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.61  
% 3.56/1.61  Inference rules
% 3.56/1.61  ----------------------
% 3.56/1.61  #Ref     : 0
% 3.56/1.61  #Sup     : 539
% 3.56/1.61  #Fact    : 0
% 3.56/1.61  #Define  : 0
% 3.56/1.61  #Split   : 0
% 3.56/1.61  #Chain   : 0
% 3.56/1.61  #Close   : 0
% 3.56/1.61  
% 3.56/1.61  Ordering : KBO
% 3.56/1.61  
% 3.56/1.61  Simplification rules
% 3.56/1.61  ----------------------
% 3.56/1.61  #Subsume      : 70
% 3.56/1.61  #Demod        : 738
% 3.56/1.61  #Tautology    : 374
% 3.56/1.61  #SimpNegUnit  : 0
% 3.56/1.61  #BackRed      : 0
% 3.56/1.61  
% 3.56/1.61  #Partial instantiations: 0
% 3.56/1.61  #Strategies tried      : 1
% 3.56/1.61  
% 3.56/1.61  Timing (in seconds)
% 3.56/1.61  ----------------------
% 3.56/1.61  Preprocessing        : 0.31
% 3.56/1.61  Parsing              : 0.17
% 3.56/1.61  CNF conversion       : 0.02
% 3.56/1.61  Main loop            : 0.55
% 3.56/1.61  Inferencing          : 0.17
% 3.56/1.61  Reduction            : 0.27
% 3.56/1.61  Demodulation         : 0.24
% 3.56/1.61  BG Simplification    : 0.02
% 3.56/1.61  Subsumption          : 0.06
% 3.56/1.61  Abstraction          : 0.03
% 3.56/1.61  MUC search           : 0.00
% 3.56/1.61  Cooper               : 0.00
% 3.56/1.61  Total                : 0.88
% 3.56/1.61  Index Insertion      : 0.00
% 3.56/1.61  Index Deletion       : 0.00
% 3.56/1.61  Index Matching       : 0.00
% 3.56/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
