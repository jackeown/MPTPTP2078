%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:23 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   53 (  69 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 108 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_110,plain,(
    ! [B_61,A_62] :
      ( k3_xboole_0(k1_relat_1(B_61),A_62) = k1_relat_1(k7_relat_1(B_61,A_62))
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    r2_hidden('#skF_1',k3_xboole_0(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_116,plain,
    ( r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_38])).

tff(c_122,plain,(
    r2_hidden('#skF_1',k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_116])).

tff(c_124,plain,(
    ! [A_63,B_64,C_65] :
      ( r2_hidden(A_63,B_64)
      | ~ r2_hidden(A_63,k1_relat_1(k7_relat_1(C_65,B_64)))
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_127,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_122,c_124])).

tff(c_130,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_127])).

tff(c_34,plain,(
    ! [B_45,A_44] :
      ( k1_funct_1(k6_relat_1(B_45),A_44) = A_44
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    ! [A_39] : v1_relat_1(k6_relat_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,(
    ! [A_39] : v1_funct_1(k6_relat_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [A_37,B_38] :
      ( k5_relat_1(k6_relat_1(A_37),B_38) = k7_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_457,plain,(
    ! [C_108,B_109,A_110] :
      ( k1_funct_1(k5_relat_1(C_108,B_109),A_110) = k1_funct_1(B_109,k1_funct_1(C_108,A_110))
      | ~ r2_hidden(A_110,k1_relat_1(k5_relat_1(C_108,B_109)))
      | ~ v1_funct_1(C_108)
      | ~ v1_relat_1(C_108)
      | ~ v1_funct_1(B_109)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_460,plain,(
    ! [A_37,B_38,A_110] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_37),B_38),A_110) = k1_funct_1(B_38,k1_funct_1(k6_relat_1(A_37),A_110))
      | ~ r2_hidden(A_110,k1_relat_1(k7_relat_1(B_38,A_37)))
      | ~ v1_funct_1(k6_relat_1(A_37))
      | ~ v1_relat_1(k6_relat_1(A_37))
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_457])).

tff(c_727,plain,(
    ! [A_119,B_120,A_121] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_119),B_120),A_121) = k1_funct_1(B_120,k1_funct_1(k6_relat_1(A_119),A_121))
      | ~ r2_hidden(A_121,k1_relat_1(k7_relat_1(B_120,A_119)))
      | ~ v1_funct_1(B_120)
      | ~ v1_relat_1(B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_460])).

tff(c_736,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'),'#skF_3'),'#skF_1') = k1_funct_1('#skF_3',k1_funct_1(k6_relat_1('#skF_2'),'#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_122,c_727])).

tff(c_740,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'),'#skF_3'),'#skF_1') = k1_funct_1('#skF_3',k1_funct_1(k6_relat_1('#skF_2'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_736])).

tff(c_36,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'),'#skF_3'),'#skF_1') != k1_funct_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_741,plain,(
    k1_funct_1('#skF_3',k1_funct_1(k6_relat_1('#skF_2'),'#skF_1')) != k1_funct_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_36])).

tff(c_753,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_741])).

tff(c_757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_753])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.64  
% 3.37/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.64  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.37/1.64  
% 3.37/1.64  %Foreground sorts:
% 3.37/1.64  
% 3.37/1.64  
% 3.37/1.64  %Background operators:
% 3.37/1.64  
% 3.37/1.64  
% 3.37/1.64  %Foreground operators:
% 3.37/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.37/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.37/1.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.37/1.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.37/1.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.37/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.37/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.37/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.37/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.37/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.37/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.37/1.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.37/1.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.37/1.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.37/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.37/1.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.37/1.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.37/1.64  
% 3.37/1.65  tff(f_87, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_1)).
% 3.37/1.65  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.37/1.65  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 3.37/1.65  tff(f_78, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_1)).
% 3.37/1.65  tff(f_61, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.37/1.65  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.37/1.65  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 3.37/1.65  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.37/1.65  tff(c_110, plain, (![B_61, A_62]: (k3_xboole_0(k1_relat_1(B_61), A_62)=k1_relat_1(k7_relat_1(B_61, A_62)) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.37/1.65  tff(c_38, plain, (r2_hidden('#skF_1', k3_xboole_0(k1_relat_1('#skF_3'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.37/1.65  tff(c_116, plain, (r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_110, c_38])).
% 3.37/1.65  tff(c_122, plain, (r2_hidden('#skF_1', k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_116])).
% 3.37/1.65  tff(c_124, plain, (![A_63, B_64, C_65]: (r2_hidden(A_63, B_64) | ~r2_hidden(A_63, k1_relat_1(k7_relat_1(C_65, B_64))) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.37/1.65  tff(c_127, plain, (r2_hidden('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_122, c_124])).
% 3.37/1.65  tff(c_130, plain, (r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_127])).
% 3.37/1.65  tff(c_34, plain, (![B_45, A_44]: (k1_funct_1(k6_relat_1(B_45), A_44)=A_44 | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.37/1.65  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.37/1.65  tff(c_28, plain, (![A_39]: (v1_relat_1(k6_relat_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.37/1.65  tff(c_30, plain, (![A_39]: (v1_funct_1(k6_relat_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.37/1.65  tff(c_26, plain, (![A_37, B_38]: (k5_relat_1(k6_relat_1(A_37), B_38)=k7_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.37/1.65  tff(c_457, plain, (![C_108, B_109, A_110]: (k1_funct_1(k5_relat_1(C_108, B_109), A_110)=k1_funct_1(B_109, k1_funct_1(C_108, A_110)) | ~r2_hidden(A_110, k1_relat_1(k5_relat_1(C_108, B_109))) | ~v1_funct_1(C_108) | ~v1_relat_1(C_108) | ~v1_funct_1(B_109) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.37/1.65  tff(c_460, plain, (![A_37, B_38, A_110]: (k1_funct_1(k5_relat_1(k6_relat_1(A_37), B_38), A_110)=k1_funct_1(B_38, k1_funct_1(k6_relat_1(A_37), A_110)) | ~r2_hidden(A_110, k1_relat_1(k7_relat_1(B_38, A_37))) | ~v1_funct_1(k6_relat_1(A_37)) | ~v1_relat_1(k6_relat_1(A_37)) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38) | ~v1_relat_1(B_38))), inference(superposition, [status(thm), theory('equality')], [c_26, c_457])).
% 3.37/1.65  tff(c_727, plain, (![A_119, B_120, A_121]: (k1_funct_1(k5_relat_1(k6_relat_1(A_119), B_120), A_121)=k1_funct_1(B_120, k1_funct_1(k6_relat_1(A_119), A_121)) | ~r2_hidden(A_121, k1_relat_1(k7_relat_1(B_120, A_119))) | ~v1_funct_1(B_120) | ~v1_relat_1(B_120))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_460])).
% 3.37/1.65  tff(c_736, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'), '#skF_3'), '#skF_1')=k1_funct_1('#skF_3', k1_funct_1(k6_relat_1('#skF_2'), '#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_122, c_727])).
% 3.37/1.65  tff(c_740, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'), '#skF_3'), '#skF_1')=k1_funct_1('#skF_3', k1_funct_1(k6_relat_1('#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_736])).
% 3.37/1.65  tff(c_36, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_2'), '#skF_3'), '#skF_1')!=k1_funct_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.37/1.65  tff(c_741, plain, (k1_funct_1('#skF_3', k1_funct_1(k6_relat_1('#skF_2'), '#skF_1'))!=k1_funct_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_740, c_36])).
% 3.37/1.65  tff(c_753, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_34, c_741])).
% 3.37/1.65  tff(c_757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_753])).
% 3.37/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.65  
% 3.37/1.65  Inference rules
% 3.37/1.65  ----------------------
% 3.37/1.65  #Ref     : 0
% 3.37/1.65  #Sup     : 177
% 3.37/1.65  #Fact    : 0
% 3.37/1.65  #Define  : 0
% 3.37/1.65  #Split   : 0
% 3.37/1.65  #Chain   : 0
% 3.37/1.65  #Close   : 0
% 3.37/1.65  
% 3.37/1.65  Ordering : KBO
% 3.37/1.65  
% 3.37/1.65  Simplification rules
% 3.37/1.65  ----------------------
% 3.37/1.65  #Subsume      : 3
% 3.37/1.65  #Demod        : 106
% 3.37/1.65  #Tautology    : 78
% 3.37/1.65  #SimpNegUnit  : 0
% 3.37/1.65  #BackRed      : 1
% 3.37/1.65  
% 3.37/1.65  #Partial instantiations: 0
% 3.37/1.65  #Strategies tried      : 1
% 3.37/1.65  
% 3.37/1.65  Timing (in seconds)
% 3.37/1.65  ----------------------
% 3.37/1.65  Preprocessing        : 0.39
% 3.37/1.65  Parsing              : 0.22
% 3.37/1.65  CNF conversion       : 0.02
% 3.37/1.65  Main loop            : 0.44
% 3.37/1.65  Inferencing          : 0.18
% 3.37/1.65  Reduction            : 0.15
% 3.37/1.65  Demodulation         : 0.12
% 3.37/1.65  BG Simplification    : 0.03
% 3.37/1.65  Subsumption          : 0.06
% 3.37/1.65  Abstraction          : 0.03
% 3.37/1.65  MUC search           : 0.00
% 3.37/1.66  Cooper               : 0.00
% 3.37/1.66  Total                : 0.86
% 3.37/1.66  Index Insertion      : 0.00
% 3.37/1.66  Index Deletion       : 0.00
% 3.37/1.66  Index Matching       : 0.00
% 3.37/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
