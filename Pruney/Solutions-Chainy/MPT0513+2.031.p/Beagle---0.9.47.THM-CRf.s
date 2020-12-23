%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:02 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   56 (  56 expanded)
%              Number of leaves         :   37 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  40 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_82,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_36,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_2'(A_43),A_43)
      | v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_195,plain,(
    ! [A_80,B_81,C_82] :
      ( ~ r1_xboole_0(A_80,B_81)
      | ~ r2_hidden(C_82,k3_xboole_0(A_80,B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_202,plain,(
    ! [A_10,C_82] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r2_hidden(C_82,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_195])).

tff(c_206,plain,(
    ! [C_83] : ~ r2_hidden(C_83,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_202])).

tff(c_211,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_206])).

tff(c_288,plain,(
    ! [B_94,A_95] :
      ( k3_xboole_0(B_94,k2_zfmisc_1(A_95,k2_relat_1(B_94))) = k7_relat_1(B_94,A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_172,plain,(
    ! [A_78,B_79] : k5_xboole_0(A_78,k3_xboole_0(A_78,B_79)) = k4_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_65,plain,(
    ! [B_67,A_68] : k5_xboole_0(B_67,A_68) = k5_xboole_0(A_68,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_81,plain,(
    ! [A_68] : k5_xboole_0(k1_xboole_0,A_68) = A_68 ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_14])).

tff(c_179,plain,(
    ! [B_79] : k4_xboole_0(k1_xboole_0,B_79) = k3_xboole_0(k1_xboole_0,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_81])).

tff(c_191,plain,(
    ! [B_79] : k3_xboole_0(k1_xboole_0,B_79) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_179])).

tff(c_301,plain,(
    ! [A_95] :
      ( k7_relat_1(k1_xboole_0,A_95) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_191])).

tff(c_317,plain,(
    ! [A_95] : k7_relat_1(k1_xboole_0,A_95) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_301])).

tff(c_40,plain,(
    k7_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.23  
% 1.90/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.23  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 1.90/1.23  
% 1.90/1.23  %Foreground sorts:
% 1.90/1.23  
% 1.90/1.23  
% 1.90/1.23  %Background operators:
% 1.90/1.23  
% 1.90/1.23  
% 1.90/1.23  %Foreground operators:
% 1.90/1.23  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.90/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.90/1.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.90/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.90/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.90/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.90/1.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.90/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.90/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.90/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.90/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.90/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.90/1.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.90/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.90/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.90/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.90/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.90/1.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.90/1.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.90/1.23  
% 2.10/1.24  tff(f_75, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.10/1.24  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.10/1.24  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.10/1.24  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.10/1.24  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 2.10/1.24  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.10/1.24  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.10/1.24  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.10/1.24  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.10/1.24  tff(f_82, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 2.10/1.24  tff(c_36, plain, (![A_43]: (r2_hidden('#skF_2'(A_43), A_43) | v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.10/1.24  tff(c_16, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.10/1.24  tff(c_10, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.10/1.24  tff(c_195, plain, (![A_80, B_81, C_82]: (~r1_xboole_0(A_80, B_81) | ~r2_hidden(C_82, k3_xboole_0(A_80, B_81)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.24  tff(c_202, plain, (![A_10, C_82]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r2_hidden(C_82, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_195])).
% 2.10/1.24  tff(c_206, plain, (![C_83]: (~r2_hidden(C_83, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_202])).
% 2.10/1.24  tff(c_211, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_206])).
% 2.10/1.24  tff(c_288, plain, (![B_94, A_95]: (k3_xboole_0(B_94, k2_zfmisc_1(A_95, k2_relat_1(B_94)))=k7_relat_1(B_94, A_95) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.10/1.24  tff(c_12, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.10/1.24  tff(c_172, plain, (![A_78, B_79]: (k5_xboole_0(A_78, k3_xboole_0(A_78, B_79))=k4_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.24  tff(c_65, plain, (![B_67, A_68]: (k5_xboole_0(B_67, A_68)=k5_xboole_0(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.24  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.10/1.24  tff(c_81, plain, (![A_68]: (k5_xboole_0(k1_xboole_0, A_68)=A_68)), inference(superposition, [status(thm), theory('equality')], [c_65, c_14])).
% 2.10/1.24  tff(c_179, plain, (![B_79]: (k4_xboole_0(k1_xboole_0, B_79)=k3_xboole_0(k1_xboole_0, B_79))), inference(superposition, [status(thm), theory('equality')], [c_172, c_81])).
% 2.10/1.24  tff(c_191, plain, (![B_79]: (k3_xboole_0(k1_xboole_0, B_79)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_179])).
% 2.10/1.24  tff(c_301, plain, (![A_95]: (k7_relat_1(k1_xboole_0, A_95)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_288, c_191])).
% 2.10/1.24  tff(c_317, plain, (![A_95]: (k7_relat_1(k1_xboole_0, A_95)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_211, c_301])).
% 2.10/1.24  tff(c_40, plain, (k7_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.10/1.24  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_317, c_40])).
% 2.10/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.24  
% 2.10/1.24  Inference rules
% 2.10/1.24  ----------------------
% 2.10/1.24  #Ref     : 0
% 2.10/1.24  #Sup     : 63
% 2.10/1.24  #Fact    : 0
% 2.10/1.24  #Define  : 0
% 2.10/1.24  #Split   : 0
% 2.10/1.24  #Chain   : 0
% 2.10/1.24  #Close   : 0
% 2.10/1.24  
% 2.10/1.24  Ordering : KBO
% 2.10/1.24  
% 2.10/1.24  Simplification rules
% 2.10/1.24  ----------------------
% 2.10/1.24  #Subsume      : 1
% 2.10/1.24  #Demod        : 21
% 2.10/1.24  #Tautology    : 49
% 2.10/1.24  #SimpNegUnit  : 2
% 2.10/1.24  #BackRed      : 1
% 2.10/1.24  
% 2.10/1.24  #Partial instantiations: 0
% 2.10/1.24  #Strategies tried      : 1
% 2.10/1.24  
% 2.10/1.24  Timing (in seconds)
% 2.10/1.24  ----------------------
% 2.10/1.24  Preprocessing        : 0.32
% 2.10/1.24  Parsing              : 0.17
% 2.10/1.24  CNF conversion       : 0.02
% 2.10/1.24  Main loop            : 0.17
% 2.10/1.24  Inferencing          : 0.06
% 2.10/1.24  Reduction            : 0.06
% 2.10/1.24  Demodulation         : 0.04
% 2.10/1.24  BG Simplification    : 0.01
% 2.10/1.24  Subsumption          : 0.02
% 2.10/1.24  Abstraction          : 0.01
% 2.10/1.24  MUC search           : 0.00
% 2.10/1.24  Cooper               : 0.00
% 2.10/1.24  Total                : 0.52
% 2.10/1.24  Index Insertion      : 0.00
% 2.10/1.24  Index Deletion       : 0.00
% 2.10/1.24  Index Matching       : 0.00
% 2.10/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
