%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:47 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   60 (  94 expanded)
%              Number of leaves         :   37 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 127 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_61,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79,plain,(
    ! [A_82,C_83,B_84] :
      ( ~ r2_hidden(A_82,C_83)
      | ~ r1_xboole_0(k2_tarski(A_82,B_84),C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_84,plain,(
    ! [A_82] : ~ r2_hidden(A_82,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_26,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_2'(A_36),A_36)
      | v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_85,plain,(
    ! [A_85] : ~ r2_hidden(A_85,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_95,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_85])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_85])).

tff(c_30,plain,(
    ! [A_54] :
      ( v1_funct_1(A_54)
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_103,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_94,c_30])).

tff(c_28,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_114,plain,(
    ! [A_89] :
      ( k1_relat_1(k6_relat_1(A_89)) = A_89
      | ~ v1_funct_1(k6_relat_1(A_89))
      | ~ v1_relat_1(k6_relat_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_117,plain,
    ( k1_relat_1(k6_relat_1(k1_xboole_0)) = k1_xboole_0
    | ~ v1_funct_1(k6_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_114])).

tff(c_119,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_103,c_28,c_28,c_117])).

tff(c_193,plain,(
    ! [A_115,B_116] :
      ( r2_hidden('#skF_5'(A_115,B_116),k1_relat_1(B_116))
      | v5_funct_1(B_116,A_115)
      | ~ v1_funct_1(B_116)
      | ~ v1_relat_1(B_116)
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_199,plain,(
    ! [A_115] :
      ( r2_hidden('#skF_5'(A_115,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_115)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_193])).

tff(c_202,plain,(
    ! [A_115] :
      ( r2_hidden('#skF_5'(A_115,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_115)
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_103,c_199])).

tff(c_204,plain,(
    ! [A_117] :
      ( v5_funct_1(k1_xboole_0,A_117)
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_202])).

tff(c_46,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_207,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_204,c_46])).

tff(c_211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.32  
% 2.23/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.33  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_4
% 2.23/1.33  
% 2.23/1.33  %Foreground sorts:
% 2.23/1.33  
% 2.23/1.33  
% 2.23/1.33  %Background operators:
% 2.23/1.33  
% 2.23/1.33  
% 2.23/1.33  %Foreground operators:
% 2.23/1.33  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.23/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.33  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.23/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.23/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.23/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.23/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.23/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.33  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.23/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.23/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.23/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.33  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.23/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.23/1.33  
% 2.23/1.34  tff(f_101, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 2.23/1.34  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.23/1.34  tff(f_50, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.23/1.34  tff(f_60, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.23/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.23/1.34  tff(f_65, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.23/1.34  tff(f_61, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.23/1.34  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.23/1.34  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.23/1.34  tff(c_50, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.23/1.34  tff(c_48, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.23/1.34  tff(c_6, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.34  tff(c_79, plain, (![A_82, C_83, B_84]: (~r2_hidden(A_82, C_83) | ~r1_xboole_0(k2_tarski(A_82, B_84), C_83))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.23/1.34  tff(c_84, plain, (![A_82]: (~r2_hidden(A_82, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_79])).
% 2.23/1.34  tff(c_26, plain, (![A_36]: (r2_hidden('#skF_2'(A_36), A_36) | v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.34  tff(c_85, plain, (![A_85]: (~r2_hidden(A_85, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_79])).
% 2.23/1.34  tff(c_95, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_85])).
% 2.23/1.34  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.34  tff(c_94, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_85])).
% 2.23/1.34  tff(c_30, plain, (![A_54]: (v1_funct_1(A_54) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.23/1.34  tff(c_103, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_94, c_30])).
% 2.23/1.34  tff(c_28, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.34  tff(c_114, plain, (![A_89]: (k1_relat_1(k6_relat_1(A_89))=A_89 | ~v1_funct_1(k6_relat_1(A_89)) | ~v1_relat_1(k6_relat_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.23/1.34  tff(c_117, plain, (k1_relat_1(k6_relat_1(k1_xboole_0))=k1_xboole_0 | ~v1_funct_1(k6_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_114])).
% 2.23/1.34  tff(c_119, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_95, c_103, c_28, c_28, c_117])).
% 2.23/1.34  tff(c_193, plain, (![A_115, B_116]: (r2_hidden('#skF_5'(A_115, B_116), k1_relat_1(B_116)) | v5_funct_1(B_116, A_115) | ~v1_funct_1(B_116) | ~v1_relat_1(B_116) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.23/1.34  tff(c_199, plain, (![A_115]: (r2_hidden('#skF_5'(A_115, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_115) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(superposition, [status(thm), theory('equality')], [c_119, c_193])).
% 2.23/1.34  tff(c_202, plain, (![A_115]: (r2_hidden('#skF_5'(A_115, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_115) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_103, c_199])).
% 2.23/1.34  tff(c_204, plain, (![A_117]: (v5_funct_1(k1_xboole_0, A_117) | ~v1_funct_1(A_117) | ~v1_relat_1(A_117))), inference(negUnitSimplification, [status(thm)], [c_84, c_202])).
% 2.23/1.34  tff(c_46, plain, (~v5_funct_1(k1_xboole_0, '#skF_7')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.23/1.34  tff(c_207, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_204, c_46])).
% 2.23/1.34  tff(c_211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_207])).
% 2.23/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.34  
% 2.23/1.34  Inference rules
% 2.23/1.34  ----------------------
% 2.23/1.34  #Ref     : 1
% 2.23/1.34  #Sup     : 33
% 2.23/1.34  #Fact    : 0
% 2.23/1.34  #Define  : 0
% 2.23/1.34  #Split   : 0
% 2.23/1.34  #Chain   : 0
% 2.23/1.34  #Close   : 0
% 2.23/1.34  
% 2.23/1.34  Ordering : KBO
% 2.23/1.34  
% 2.23/1.34  Simplification rules
% 2.23/1.34  ----------------------
% 2.23/1.34  #Subsume      : 1
% 2.23/1.34  #Demod        : 23
% 2.23/1.34  #Tautology    : 21
% 2.23/1.34  #SimpNegUnit  : 3
% 2.23/1.34  #BackRed      : 0
% 2.23/1.34  
% 2.23/1.34  #Partial instantiations: 0
% 2.23/1.34  #Strategies tried      : 1
% 2.23/1.34  
% 2.23/1.34  Timing (in seconds)
% 2.23/1.34  ----------------------
% 2.23/1.34  Preprocessing        : 0.36
% 2.23/1.34  Parsing              : 0.19
% 2.23/1.34  CNF conversion       : 0.03
% 2.23/1.34  Main loop            : 0.17
% 2.23/1.34  Inferencing          : 0.07
% 2.23/1.34  Reduction            : 0.05
% 2.23/1.34  Demodulation         : 0.04
% 2.23/1.34  BG Simplification    : 0.02
% 2.23/1.34  Subsumption          : 0.02
% 2.23/1.34  Abstraction          : 0.01
% 2.23/1.35  MUC search           : 0.00
% 2.23/1.35  Cooper               : 0.00
% 2.23/1.35  Total                : 0.56
% 2.23/1.35  Index Insertion      : 0.00
% 2.23/1.35  Index Deletion       : 0.00
% 2.23/1.35  Index Matching       : 0.00
% 2.23/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
