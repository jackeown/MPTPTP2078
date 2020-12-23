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
% DateTime   : Thu Dec  3 10:04:28 EST 2020

% Result     : Theorem 9.62s
% Output     : CNFRefutation 9.62s
% Verified   : 
% Statistics : Number of formulae       :   48 (  55 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   75 ( 105 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_62,plain,(
    ! [A_30,B_31,C_32] :
      ( ~ r1_xboole_0(A_30,B_31)
      | ~ r2_hidden(C_32,k3_xboole_0(A_30,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_69,plain,(
    ! [A_11,C_32] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_32,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_62])).

tff(c_72,plain,(
    ! [C_32] : ~ r2_hidden(C_32,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_69])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_70,plain,(
    ! [A_30,B_31,A_1] :
      ( ~ r1_xboole_0(A_30,B_31)
      | r1_xboole_0(A_1,k3_xboole_0(A_30,B_31)) ) ),
    inference(resolution,[status(thm)],[c_4,c_62])).

tff(c_161,plain,(
    ! [B_53,A_54] :
      ( k9_relat_1(B_53,A_54) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_53),A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_174,plain,(
    ! [B_53,A_30,B_31] :
      ( k9_relat_1(B_53,k3_xboole_0(A_30,B_31)) = k1_xboole_0
      | ~ v1_relat_1(B_53)
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_70,c_161])).

tff(c_181,plain,(
    ! [C_56,A_57,B_58] :
      ( k3_xboole_0(k9_relat_1(C_56,A_57),k9_relat_1(C_56,B_58)) = k9_relat_1(C_56,k3_xboole_0(A_57,B_58))
      | ~ v2_funct_1(C_56)
      | ~ v1_funct_1(C_56)
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),k3_xboole_0(A_6,B_7))
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2174,plain,(
    ! [C_130,A_131,B_132] :
      ( r2_hidden('#skF_2'(k9_relat_1(C_130,A_131),k9_relat_1(C_130,B_132)),k9_relat_1(C_130,k3_xboole_0(A_131,B_132)))
      | r1_xboole_0(k9_relat_1(C_130,A_131),k9_relat_1(C_130,B_132))
      | ~ v2_funct_1(C_130)
      | ~ v1_funct_1(C_130)
      | ~ v1_relat_1(C_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_8])).

tff(c_2341,plain,(
    ! [B_53,A_30,B_31] :
      ( r2_hidden('#skF_2'(k9_relat_1(B_53,A_30),k9_relat_1(B_53,B_31)),k1_xboole_0)
      | r1_xboole_0(k9_relat_1(B_53,A_30),k9_relat_1(B_53,B_31))
      | ~ v2_funct_1(B_53)
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(B_53)
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_2174])).

tff(c_23889,plain,(
    ! [B_477,A_478,B_479] :
      ( r1_xboole_0(k9_relat_1(B_477,A_478),k9_relat_1(B_477,B_479))
      | ~ v2_funct_1(B_477)
      | ~ v1_funct_1(B_477)
      | ~ v1_relat_1(B_477)
      | ~ v1_relat_1(B_477)
      | ~ r1_xboole_0(A_478,B_479) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2341])).

tff(c_26,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_23900,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_23889,c_26])).

tff(c_24274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_32,c_28,c_23900])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:02:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.62/3.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.62/3.81  
% 9.62/3.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.62/3.81  %$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 9.62/3.81  
% 9.62/3.81  %Foreground sorts:
% 9.62/3.81  
% 9.62/3.81  
% 9.62/3.81  %Background operators:
% 9.62/3.81  
% 9.62/3.81  
% 9.62/3.81  %Foreground operators:
% 9.62/3.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.62/3.81  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.62/3.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.62/3.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.62/3.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.62/3.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.62/3.81  tff('#skF_5', type, '#skF_5': $i).
% 9.62/3.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.62/3.81  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.62/3.81  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.62/3.81  tff('#skF_3', type, '#skF_3': $i).
% 9.62/3.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.62/3.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.62/3.81  tff('#skF_4', type, '#skF_4': $i).
% 9.62/3.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.62/3.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.62/3.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.62/3.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.62/3.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.62/3.81  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.62/3.81  
% 9.62/3.83  tff(f_90, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_funct_1)).
% 9.62/3.83  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 9.62/3.83  tff(f_59, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 9.62/3.83  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.62/3.83  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.62/3.83  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 9.62/3.83  tff(f_79, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_1)).
% 9.62/3.83  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.62/3.83  tff(c_34, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.62/3.83  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.62/3.83  tff(c_28, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.62/3.83  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.62/3.83  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.62/3.83  tff(c_62, plain, (![A_30, B_31, C_32]: (~r1_xboole_0(A_30, B_31) | ~r2_hidden(C_32, k3_xboole_0(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.62/3.83  tff(c_69, plain, (![A_11, C_32]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_62])).
% 9.62/3.83  tff(c_72, plain, (![C_32]: (~r2_hidden(C_32, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_69])).
% 9.62/3.83  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.62/3.83  tff(c_70, plain, (![A_30, B_31, A_1]: (~r1_xboole_0(A_30, B_31) | r1_xboole_0(A_1, k3_xboole_0(A_30, B_31)))), inference(resolution, [status(thm)], [c_4, c_62])).
% 9.62/3.83  tff(c_161, plain, (![B_53, A_54]: (k9_relat_1(B_53, A_54)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_53), A_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.62/3.83  tff(c_174, plain, (![B_53, A_30, B_31]: (k9_relat_1(B_53, k3_xboole_0(A_30, B_31))=k1_xboole_0 | ~v1_relat_1(B_53) | ~r1_xboole_0(A_30, B_31))), inference(resolution, [status(thm)], [c_70, c_161])).
% 9.62/3.83  tff(c_181, plain, (![C_56, A_57, B_58]: (k3_xboole_0(k9_relat_1(C_56, A_57), k9_relat_1(C_56, B_58))=k9_relat_1(C_56, k3_xboole_0(A_57, B_58)) | ~v2_funct_1(C_56) | ~v1_funct_1(C_56) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.62/3.83  tff(c_8, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), k3_xboole_0(A_6, B_7)) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.62/3.83  tff(c_2174, plain, (![C_130, A_131, B_132]: (r2_hidden('#skF_2'(k9_relat_1(C_130, A_131), k9_relat_1(C_130, B_132)), k9_relat_1(C_130, k3_xboole_0(A_131, B_132))) | r1_xboole_0(k9_relat_1(C_130, A_131), k9_relat_1(C_130, B_132)) | ~v2_funct_1(C_130) | ~v1_funct_1(C_130) | ~v1_relat_1(C_130))), inference(superposition, [status(thm), theory('equality')], [c_181, c_8])).
% 9.62/3.83  tff(c_2341, plain, (![B_53, A_30, B_31]: (r2_hidden('#skF_2'(k9_relat_1(B_53, A_30), k9_relat_1(B_53, B_31)), k1_xboole_0) | r1_xboole_0(k9_relat_1(B_53, A_30), k9_relat_1(B_53, B_31)) | ~v2_funct_1(B_53) | ~v1_funct_1(B_53) | ~v1_relat_1(B_53) | ~v1_relat_1(B_53) | ~r1_xboole_0(A_30, B_31))), inference(superposition, [status(thm), theory('equality')], [c_174, c_2174])).
% 9.62/3.83  tff(c_23889, plain, (![B_477, A_478, B_479]: (r1_xboole_0(k9_relat_1(B_477, A_478), k9_relat_1(B_477, B_479)) | ~v2_funct_1(B_477) | ~v1_funct_1(B_477) | ~v1_relat_1(B_477) | ~v1_relat_1(B_477) | ~r1_xboole_0(A_478, B_479))), inference(negUnitSimplification, [status(thm)], [c_72, c_2341])).
% 9.62/3.83  tff(c_26, plain, (~r1_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.62/3.83  tff(c_23900, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_23889, c_26])).
% 9.62/3.83  tff(c_24274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_32, c_28, c_23900])).
% 9.62/3.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.62/3.83  
% 9.62/3.83  Inference rules
% 9.62/3.83  ----------------------
% 9.62/3.83  #Ref     : 0
% 9.62/3.83  #Sup     : 5591
% 9.62/3.83  #Fact    : 0
% 9.62/3.83  #Define  : 0
% 9.62/3.83  #Split   : 0
% 9.62/3.83  #Chain   : 0
% 9.62/3.83  #Close   : 0
% 9.62/3.83  
% 9.62/3.83  Ordering : KBO
% 9.62/3.83  
% 9.62/3.83  Simplification rules
% 9.62/3.83  ----------------------
% 9.62/3.83  #Subsume      : 575
% 9.62/3.83  #Demod        : 7709
% 9.62/3.83  #Tautology    : 4237
% 9.62/3.83  #SimpNegUnit  : 147
% 9.62/3.83  #BackRed      : 1
% 9.62/3.83  
% 9.62/3.83  #Partial instantiations: 0
% 9.62/3.83  #Strategies tried      : 1
% 9.62/3.83  
% 9.62/3.83  Timing (in seconds)
% 9.62/3.83  ----------------------
% 9.62/3.83  Preprocessing        : 0.32
% 9.62/3.83  Parsing              : 0.18
% 9.62/3.83  CNF conversion       : 0.02
% 9.62/3.83  Main loop            : 2.73
% 9.62/3.83  Inferencing          : 0.72
% 9.62/3.83  Reduction            : 1.41
% 9.62/3.83  Demodulation         : 1.23
% 9.62/3.83  BG Simplification    : 0.05
% 9.62/3.83  Subsumption          : 0.42
% 9.62/3.83  Abstraction          : 0.10
% 9.62/3.83  MUC search           : 0.00
% 9.62/3.83  Cooper               : 0.00
% 9.62/3.83  Total                : 3.08
% 9.62/3.83  Index Insertion      : 0.00
% 9.62/3.83  Index Deletion       : 0.00
% 9.62/3.83  Index Matching       : 0.00
% 9.62/3.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
