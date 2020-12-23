%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:48 EST 2020

% Result     : Theorem 4.44s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :   57 (  63 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 103 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v5_relat_1(C,A) )
           => v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t218_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_34,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_85,plain,(
    ! [B_38,A_39] :
      ( ~ r2_hidden(B_38,A_39)
      | k4_xboole_0(A_39,k1_tarski(B_38)) != A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_91,plain,(
    ! [B_40] : ~ r2_hidden(B_40,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_85])).

tff(c_101,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_40,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_176,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(k2_relat_1(B_52),A_53)
      | ~ v5_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_388,plain,(
    ! [B_67,A_68] :
      ( k4_xboole_0(k2_relat_1(B_67),A_68) = k1_xboole_0
      | ~ v5_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_176,c_18])).

tff(c_20,plain,(
    ! [C_14,B_13,A_12] :
      ( r1_tarski(k4_xboole_0(C_14,B_13),k4_xboole_0(C_14,A_12))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2745,plain,(
    ! [B_174,B_175,A_176] :
      ( r1_tarski(k4_xboole_0(k2_relat_1(B_174),B_175),k1_xboole_0)
      | ~ r1_tarski(A_176,B_175)
      | ~ v5_relat_1(B_174,A_176)
      | ~ v1_relat_1(B_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_20])).

tff(c_2833,plain,(
    ! [B_178] :
      ( r1_tarski(k4_xboole_0(k2_relat_1(B_178),'#skF_4'),k1_xboole_0)
      | ~ v5_relat_1(B_178,'#skF_3')
      | ~ v1_relat_1(B_178) ) ),
    inference(resolution,[status(thm)],[c_40,c_2745])).

tff(c_134,plain,(
    ! [A_46,B_47] :
      ( r2_xboole_0(A_46,B_47)
      | B_47 = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_79,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_2'(A_34,B_35),B_35)
      | ~ r2_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    ! [B_35,A_34] :
      ( ~ v1_xboole_0(B_35)
      | ~ r2_xboole_0(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_79,c_2])).

tff(c_150,plain,(
    ! [B_47,A_46] :
      ( ~ v1_xboole_0(B_47)
      | B_47 = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_134,c_83])).

tff(c_2847,plain,(
    ! [B_178] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k4_xboole_0(k2_relat_1(B_178),'#skF_4') = k1_xboole_0
      | ~ v5_relat_1(B_178,'#skF_3')
      | ~ v1_relat_1(B_178) ) ),
    inference(resolution,[status(thm)],[c_2833,c_150])).

tff(c_2869,plain,(
    ! [B_179] :
      ( k4_xboole_0(k2_relat_1(B_179),'#skF_4') = k1_xboole_0
      | ~ v5_relat_1(B_179,'#skF_3')
      | ~ v1_relat_1(B_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_2847])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_195,plain,(
    ! [B_56,A_57] :
      ( v5_relat_1(B_56,A_57)
      | ~ r1_tarski(k2_relat_1(B_56),A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_204,plain,(
    ! [B_56,B_11] :
      ( v5_relat_1(B_56,B_11)
      | ~ v1_relat_1(B_56)
      | k4_xboole_0(k2_relat_1(B_56),B_11) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_195])).

tff(c_2908,plain,(
    ! [B_180] :
      ( v5_relat_1(B_180,'#skF_4')
      | ~ v5_relat_1(B_180,'#skF_3')
      | ~ v1_relat_1(B_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2869,c_204])).

tff(c_2911,plain,
    ( v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_2908])).

tff(c_2914,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2911])).

tff(c_2916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_2914])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:53:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.44/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.44/1.82  
% 4.44/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.82  %$ v5_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 4.60/1.82  
% 4.60/1.82  %Foreground sorts:
% 4.60/1.82  
% 4.60/1.82  
% 4.60/1.82  %Background operators:
% 4.60/1.82  
% 4.60/1.82  
% 4.60/1.82  %Foreground operators:
% 4.60/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.60/1.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.60/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.60/1.82  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.60/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.60/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.60/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.60/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.60/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.60/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.60/1.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.60/1.82  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 4.60/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.60/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.60/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.82  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.60/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.60/1.82  
% 4.66/1.84  tff(f_81, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v5_relat_1(C, A)) => v5_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t218_relat_1)).
% 4.66/1.84  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.66/1.84  tff(f_58, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 4.66/1.84  tff(f_65, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.66/1.84  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.66/1.84  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.66/1.84  tff(f_56, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 4.66/1.84  tff(f_38, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 4.66/1.84  tff(f_48, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 4.66/1.84  tff(c_34, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.66/1.84  tff(c_38, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.66/1.84  tff(c_36, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.66/1.84  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.66/1.84  tff(c_22, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.66/1.84  tff(c_85, plain, (![B_38, A_39]: (~r2_hidden(B_38, A_39) | k4_xboole_0(A_39, k1_tarski(B_38))!=A_39)), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.66/1.84  tff(c_91, plain, (![B_40]: (~r2_hidden(B_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_85])).
% 4.66/1.84  tff(c_101, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_91])).
% 4.66/1.84  tff(c_40, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.66/1.84  tff(c_176, plain, (![B_52, A_53]: (r1_tarski(k2_relat_1(B_52), A_53) | ~v5_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.66/1.84  tff(c_18, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.66/1.84  tff(c_388, plain, (![B_67, A_68]: (k4_xboole_0(k2_relat_1(B_67), A_68)=k1_xboole_0 | ~v5_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_176, c_18])).
% 4.66/1.84  tff(c_20, plain, (![C_14, B_13, A_12]: (r1_tarski(k4_xboole_0(C_14, B_13), k4_xboole_0(C_14, A_12)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.66/1.84  tff(c_2745, plain, (![B_174, B_175, A_176]: (r1_tarski(k4_xboole_0(k2_relat_1(B_174), B_175), k1_xboole_0) | ~r1_tarski(A_176, B_175) | ~v5_relat_1(B_174, A_176) | ~v1_relat_1(B_174))), inference(superposition, [status(thm), theory('equality')], [c_388, c_20])).
% 4.66/1.84  tff(c_2833, plain, (![B_178]: (r1_tarski(k4_xboole_0(k2_relat_1(B_178), '#skF_4'), k1_xboole_0) | ~v5_relat_1(B_178, '#skF_3') | ~v1_relat_1(B_178))), inference(resolution, [status(thm)], [c_40, c_2745])).
% 4.66/1.84  tff(c_134, plain, (![A_46, B_47]: (r2_xboole_0(A_46, B_47) | B_47=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.66/1.84  tff(c_79, plain, (![A_34, B_35]: (r2_hidden('#skF_2'(A_34, B_35), B_35) | ~r2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.66/1.84  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.66/1.84  tff(c_83, plain, (![B_35, A_34]: (~v1_xboole_0(B_35) | ~r2_xboole_0(A_34, B_35))), inference(resolution, [status(thm)], [c_79, c_2])).
% 4.66/1.84  tff(c_150, plain, (![B_47, A_46]: (~v1_xboole_0(B_47) | B_47=A_46 | ~r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_134, c_83])).
% 4.66/1.84  tff(c_2847, plain, (![B_178]: (~v1_xboole_0(k1_xboole_0) | k4_xboole_0(k2_relat_1(B_178), '#skF_4')=k1_xboole_0 | ~v5_relat_1(B_178, '#skF_3') | ~v1_relat_1(B_178))), inference(resolution, [status(thm)], [c_2833, c_150])).
% 4.66/1.84  tff(c_2869, plain, (![B_179]: (k4_xboole_0(k2_relat_1(B_179), '#skF_4')=k1_xboole_0 | ~v5_relat_1(B_179, '#skF_3') | ~v1_relat_1(B_179))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_2847])).
% 4.66/1.84  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.66/1.84  tff(c_195, plain, (![B_56, A_57]: (v5_relat_1(B_56, A_57) | ~r1_tarski(k2_relat_1(B_56), A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.66/1.84  tff(c_204, plain, (![B_56, B_11]: (v5_relat_1(B_56, B_11) | ~v1_relat_1(B_56) | k4_xboole_0(k2_relat_1(B_56), B_11)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_195])).
% 4.66/1.84  tff(c_2908, plain, (![B_180]: (v5_relat_1(B_180, '#skF_4') | ~v5_relat_1(B_180, '#skF_3') | ~v1_relat_1(B_180))), inference(superposition, [status(thm), theory('equality')], [c_2869, c_204])).
% 4.66/1.84  tff(c_2911, plain, (v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_36, c_2908])).
% 4.66/1.84  tff(c_2914, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2911])).
% 4.66/1.84  tff(c_2916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_2914])).
% 4.66/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.84  
% 4.66/1.84  Inference rules
% 4.66/1.84  ----------------------
% 4.66/1.84  #Ref     : 0
% 4.66/1.84  #Sup     : 649
% 4.66/1.84  #Fact    : 0
% 4.66/1.84  #Define  : 0
% 4.66/1.84  #Split   : 13
% 4.66/1.84  #Chain   : 0
% 4.66/1.84  #Close   : 0
% 4.66/1.84  
% 4.66/1.84  Ordering : KBO
% 4.66/1.84  
% 4.66/1.84  Simplification rules
% 4.66/1.84  ----------------------
% 4.66/1.84  #Subsume      : 197
% 4.66/1.84  #Demod        : 305
% 4.66/1.84  #Tautology    : 220
% 4.66/1.84  #SimpNegUnit  : 42
% 4.66/1.84  #BackRed      : 42
% 4.66/1.84  
% 4.66/1.84  #Partial instantiations: 0
% 4.66/1.84  #Strategies tried      : 1
% 4.66/1.84  
% 4.66/1.84  Timing (in seconds)
% 4.66/1.84  ----------------------
% 4.66/1.85  Preprocessing        : 0.31
% 4.66/1.85  Parsing              : 0.16
% 4.66/1.85  CNF conversion       : 0.02
% 4.66/1.85  Main loop            : 0.75
% 4.66/1.85  Inferencing          : 0.24
% 4.66/1.85  Reduction            : 0.22
% 4.66/1.85  Demodulation         : 0.14
% 4.66/1.85  BG Simplification    : 0.03
% 4.66/1.85  Subsumption          : 0.20
% 4.66/1.85  Abstraction          : 0.03
% 4.66/1.85  MUC search           : 0.00
% 4.66/1.85  Cooper               : 0.00
% 4.66/1.85  Total                : 1.12
% 4.66/1.85  Index Insertion      : 0.00
% 4.66/1.85  Index Deletion       : 0.00
% 4.66/1.85  Index Matching       : 0.00
% 4.66/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
