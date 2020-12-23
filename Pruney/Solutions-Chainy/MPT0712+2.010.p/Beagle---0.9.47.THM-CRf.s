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
% DateTime   : Thu Dec  3 10:05:32 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 146 expanded)
%              Number of leaves         :   35 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :  141 ( 310 expanded)
%              Number of equality atoms :   30 (  63 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_84,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_125,plain,(
    ! [B_49,A_50] :
      ( v4_relat_1(B_49,A_50)
      | ~ r1_tarski(k1_relat_1(B_49),A_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_135,plain,(
    ! [B_49] :
      ( v4_relat_1(B_49,k1_relat_1(B_49))
      | ~ v1_relat_1(B_49) ) ),
    inference(resolution,[status(thm)],[c_6,c_125])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_961,plain,(
    ! [A_151,C_152,B_153] :
      ( r1_xboole_0(k2_tarski(A_151,C_152),B_153)
      | r2_hidden(C_152,B_153)
      | r2_hidden(A_151,B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_964,plain,(
    ! [A_4,B_153] :
      ( r1_xboole_0(k1_tarski(A_4),B_153)
      | r2_hidden(A_4,B_153)
      | r2_hidden(A_4,B_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_961])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(k7_relat_1(A_19,B_20))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [C_23,A_21,B_22] :
      ( v4_relat_1(k7_relat_1(C_23,A_21),B_22)
      | ~ v4_relat_1(C_23,B_22)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_809,plain,(
    ! [B_138,A_139] :
      ( k7_relat_1(B_138,A_139) = B_138
      | ~ r1_tarski(k1_relat_1(B_138),A_139)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_916,plain,(
    ! [B_148,A_149] :
      ( k7_relat_1(B_148,A_149) = B_148
      | ~ v4_relat_1(B_148,A_149)
      | ~ v1_relat_1(B_148) ) ),
    inference(resolution,[status(thm)],[c_22,c_809])).

tff(c_2928,plain,(
    ! [C_261,A_262,B_263] :
      ( k7_relat_1(k7_relat_1(C_261,A_262),B_263) = k7_relat_1(C_261,A_262)
      | ~ v1_relat_1(k7_relat_1(C_261,A_262))
      | ~ v4_relat_1(C_261,B_263)
      | ~ v1_relat_1(C_261) ) ),
    inference(resolution,[status(thm)],[c_26,c_916])).

tff(c_2962,plain,(
    ! [A_264,B_265,B_266] :
      ( k7_relat_1(k7_relat_1(A_264,B_265),B_266) = k7_relat_1(A_264,B_265)
      | ~ v4_relat_1(A_264,B_266)
      | ~ v1_relat_1(A_264) ) ),
    inference(resolution,[status(thm)],[c_24,c_2928])).

tff(c_32,plain,(
    ! [B_25,A_24] :
      ( k2_relat_1(k7_relat_1(B_25,A_24)) = k9_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10155,plain,(
    ! [A_386,B_387,B_388] :
      ( k9_relat_1(k7_relat_1(A_386,B_387),B_388) = k2_relat_1(k7_relat_1(A_386,B_387))
      | ~ v1_relat_1(k7_relat_1(A_386,B_387))
      | ~ v4_relat_1(A_386,B_388)
      | ~ v1_relat_1(A_386) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2962,c_32])).

tff(c_10221,plain,(
    ! [A_389,B_390,B_391] :
      ( k9_relat_1(k7_relat_1(A_389,B_390),B_391) = k2_relat_1(k7_relat_1(A_389,B_390))
      | ~ v4_relat_1(A_389,B_391)
      | ~ v1_relat_1(A_389) ) ),
    inference(resolution,[status(thm)],[c_24,c_10155])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_966,plain,(
    ! [C_156,A_157,B_158] :
      ( k7_relat_1(k7_relat_1(C_156,A_157),B_158) = k1_xboole_0
      | ~ r1_xboole_0(A_157,B_158)
      | ~ v1_relat_1(C_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_985,plain,(
    ! [C_156,A_157,B_158] :
      ( k9_relat_1(k7_relat_1(C_156,A_157),B_158) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k7_relat_1(C_156,A_157))
      | ~ r1_xboole_0(A_157,B_158)
      | ~ v1_relat_1(C_156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_966,c_32])).

tff(c_1162,plain,(
    ! [C_174,A_175,B_176] :
      ( k9_relat_1(k7_relat_1(C_174,A_175),B_176) = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1(C_174,A_175))
      | ~ r1_xboole_0(A_175,B_176)
      | ~ v1_relat_1(C_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_985])).

tff(c_1175,plain,(
    ! [A_19,B_20,B_176] :
      ( k9_relat_1(k7_relat_1(A_19,B_20),B_176) = k1_xboole_0
      | ~ r1_xboole_0(B_20,B_176)
      | ~ v1_relat_1(A_19) ) ),
    inference(resolution,[status(thm)],[c_24,c_1162])).

tff(c_10412,plain,(
    ! [A_392,B_393,B_394] :
      ( k2_relat_1(k7_relat_1(A_392,B_393)) = k1_xboole_0
      | ~ r1_xboole_0(B_393,B_394)
      | ~ v1_relat_1(A_392)
      | ~ v4_relat_1(A_392,B_394)
      | ~ v1_relat_1(A_392) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10221,c_1175])).

tff(c_10428,plain,(
    ! [A_395,A_396,B_397] :
      ( k2_relat_1(k7_relat_1(A_395,k1_tarski(A_396))) = k1_xboole_0
      | ~ v4_relat_1(A_395,B_397)
      | ~ v1_relat_1(A_395)
      | r2_hidden(A_396,B_397) ) ),
    inference(resolution,[status(thm)],[c_964,c_10412])).

tff(c_10464,plain,(
    ! [B_398,A_399] :
      ( k2_relat_1(k7_relat_1(B_398,k1_tarski(A_399))) = k1_xboole_0
      | r2_hidden(A_399,k1_relat_1(B_398))
      | ~ v1_relat_1(B_398) ) ),
    inference(resolution,[status(thm)],[c_135,c_10428])).

tff(c_44,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10498,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10464,c_44])).

tff(c_10598,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8,c_10498])).

tff(c_1024,plain,(
    ! [C_163,A_164,B_165] :
      ( k2_tarski(k1_funct_1(C_163,A_164),k1_funct_1(C_163,B_165)) = k9_relat_1(C_163,k2_tarski(A_164,B_165))
      | ~ r2_hidden(B_165,k1_relat_1(C_163))
      | ~ r2_hidden(A_164,k1_relat_1(C_163))
      | ~ v1_funct_1(C_163)
      | ~ v1_relat_1(C_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1034,plain,(
    ! [C_163,B_165] :
      ( k9_relat_1(C_163,k2_tarski(B_165,B_165)) = k1_tarski(k1_funct_1(C_163,B_165))
      | ~ r2_hidden(B_165,k1_relat_1(C_163))
      | ~ r2_hidden(B_165,k1_relat_1(C_163))
      | ~ v1_funct_1(C_163)
      | ~ v1_relat_1(C_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1024,c_10])).

tff(c_1043,plain,(
    ! [C_163,B_165] :
      ( k9_relat_1(C_163,k1_tarski(B_165)) = k1_tarski(k1_funct_1(C_163,B_165))
      | ~ r2_hidden(B_165,k1_relat_1(C_163))
      | ~ r2_hidden(B_165,k1_relat_1(C_163))
      | ~ v1_funct_1(C_163)
      | ~ v1_relat_1(C_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1034])).

tff(c_10614,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_tarski(k1_funct_1('#skF_2','#skF_1'))
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10598,c_1043])).

tff(c_10617,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_tarski(k1_funct_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_10598,c_10614])).

tff(c_111,plain,(
    ! [B_47,A_48] :
      ( k2_relat_1(k7_relat_1(B_47,A_48)) = k9_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_117,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_44])).

tff(c_123,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_117])).

tff(c_10756,plain,(
    ~ r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10617,c_123])).

tff(c_10759,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.59/2.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.84  
% 7.59/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.84  %$ v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.59/2.84  
% 7.59/2.84  %Foreground sorts:
% 7.59/2.84  
% 7.59/2.84  
% 7.59/2.84  %Background operators:
% 7.59/2.84  
% 7.59/2.84  
% 7.59/2.84  %Foreground operators:
% 7.59/2.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.59/2.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.59/2.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.59/2.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.59/2.84  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.59/2.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.59/2.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.59/2.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.59/2.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.59/2.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.59/2.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.59/2.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.59/2.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.59/2.84  tff('#skF_2', type, '#skF_2': $i).
% 7.59/2.84  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.59/2.84  tff('#skF_1', type, '#skF_1': $i).
% 7.59/2.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.59/2.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.59/2.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.59/2.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.59/2.84  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.59/2.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.59/2.84  
% 7.59/2.86  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.59/2.86  tff(f_107, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 7.59/2.86  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.59/2.86  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.59/2.86  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.59/2.86  tff(f_51, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 7.59/2.86  tff(f_61, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 7.59/2.86  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc23_relat_1)).
% 7.59/2.86  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 7.59/2.86  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 7.59/2.86  tff(f_84, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 7.59/2.86  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 7.59/2.86  tff(f_100, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_funct_1)).
% 7.59/2.86  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.59/2.86  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.59/2.86  tff(c_46, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.59/2.86  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.59/2.86  tff(c_125, plain, (![B_49, A_50]: (v4_relat_1(B_49, A_50) | ~r1_tarski(k1_relat_1(B_49), A_50) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.59/2.86  tff(c_135, plain, (![B_49]: (v4_relat_1(B_49, k1_relat_1(B_49)) | ~v1_relat_1(B_49))), inference(resolution, [status(thm)], [c_6, c_125])).
% 7.59/2.86  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.59/2.86  tff(c_961, plain, (![A_151, C_152, B_153]: (r1_xboole_0(k2_tarski(A_151, C_152), B_153) | r2_hidden(C_152, B_153) | r2_hidden(A_151, B_153))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.59/2.86  tff(c_964, plain, (![A_4, B_153]: (r1_xboole_0(k1_tarski(A_4), B_153) | r2_hidden(A_4, B_153) | r2_hidden(A_4, B_153))), inference(superposition, [status(thm), theory('equality')], [c_10, c_961])).
% 7.59/2.86  tff(c_24, plain, (![A_19, B_20]: (v1_relat_1(k7_relat_1(A_19, B_20)) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.59/2.86  tff(c_26, plain, (![C_23, A_21, B_22]: (v4_relat_1(k7_relat_1(C_23, A_21), B_22) | ~v4_relat_1(C_23, B_22) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.59/2.86  tff(c_22, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(B_18), A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.59/2.86  tff(c_809, plain, (![B_138, A_139]: (k7_relat_1(B_138, A_139)=B_138 | ~r1_tarski(k1_relat_1(B_138), A_139) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.59/2.86  tff(c_916, plain, (![B_148, A_149]: (k7_relat_1(B_148, A_149)=B_148 | ~v4_relat_1(B_148, A_149) | ~v1_relat_1(B_148))), inference(resolution, [status(thm)], [c_22, c_809])).
% 7.59/2.86  tff(c_2928, plain, (![C_261, A_262, B_263]: (k7_relat_1(k7_relat_1(C_261, A_262), B_263)=k7_relat_1(C_261, A_262) | ~v1_relat_1(k7_relat_1(C_261, A_262)) | ~v4_relat_1(C_261, B_263) | ~v1_relat_1(C_261))), inference(resolution, [status(thm)], [c_26, c_916])).
% 7.59/2.86  tff(c_2962, plain, (![A_264, B_265, B_266]: (k7_relat_1(k7_relat_1(A_264, B_265), B_266)=k7_relat_1(A_264, B_265) | ~v4_relat_1(A_264, B_266) | ~v1_relat_1(A_264))), inference(resolution, [status(thm)], [c_24, c_2928])).
% 7.59/2.86  tff(c_32, plain, (![B_25, A_24]: (k2_relat_1(k7_relat_1(B_25, A_24))=k9_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.59/2.86  tff(c_10155, plain, (![A_386, B_387, B_388]: (k9_relat_1(k7_relat_1(A_386, B_387), B_388)=k2_relat_1(k7_relat_1(A_386, B_387)) | ~v1_relat_1(k7_relat_1(A_386, B_387)) | ~v4_relat_1(A_386, B_388) | ~v1_relat_1(A_386))), inference(superposition, [status(thm), theory('equality')], [c_2962, c_32])).
% 7.59/2.86  tff(c_10221, plain, (![A_389, B_390, B_391]: (k9_relat_1(k7_relat_1(A_389, B_390), B_391)=k2_relat_1(k7_relat_1(A_389, B_390)) | ~v4_relat_1(A_389, B_391) | ~v1_relat_1(A_389))), inference(resolution, [status(thm)], [c_24, c_10155])).
% 7.59/2.86  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.59/2.86  tff(c_966, plain, (![C_156, A_157, B_158]: (k7_relat_1(k7_relat_1(C_156, A_157), B_158)=k1_xboole_0 | ~r1_xboole_0(A_157, B_158) | ~v1_relat_1(C_156))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.59/2.86  tff(c_985, plain, (![C_156, A_157, B_158]: (k9_relat_1(k7_relat_1(C_156, A_157), B_158)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k7_relat_1(C_156, A_157)) | ~r1_xboole_0(A_157, B_158) | ~v1_relat_1(C_156))), inference(superposition, [status(thm), theory('equality')], [c_966, c_32])).
% 7.59/2.86  tff(c_1162, plain, (![C_174, A_175, B_176]: (k9_relat_1(k7_relat_1(C_174, A_175), B_176)=k1_xboole_0 | ~v1_relat_1(k7_relat_1(C_174, A_175)) | ~r1_xboole_0(A_175, B_176) | ~v1_relat_1(C_174))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_985])).
% 7.59/2.86  tff(c_1175, plain, (![A_19, B_20, B_176]: (k9_relat_1(k7_relat_1(A_19, B_20), B_176)=k1_xboole_0 | ~r1_xboole_0(B_20, B_176) | ~v1_relat_1(A_19))), inference(resolution, [status(thm)], [c_24, c_1162])).
% 7.59/2.86  tff(c_10412, plain, (![A_392, B_393, B_394]: (k2_relat_1(k7_relat_1(A_392, B_393))=k1_xboole_0 | ~r1_xboole_0(B_393, B_394) | ~v1_relat_1(A_392) | ~v4_relat_1(A_392, B_394) | ~v1_relat_1(A_392))), inference(superposition, [status(thm), theory('equality')], [c_10221, c_1175])).
% 7.59/2.86  tff(c_10428, plain, (![A_395, A_396, B_397]: (k2_relat_1(k7_relat_1(A_395, k1_tarski(A_396)))=k1_xboole_0 | ~v4_relat_1(A_395, B_397) | ~v1_relat_1(A_395) | r2_hidden(A_396, B_397))), inference(resolution, [status(thm)], [c_964, c_10412])).
% 7.59/2.86  tff(c_10464, plain, (![B_398, A_399]: (k2_relat_1(k7_relat_1(B_398, k1_tarski(A_399)))=k1_xboole_0 | r2_hidden(A_399, k1_relat_1(B_398)) | ~v1_relat_1(B_398))), inference(resolution, [status(thm)], [c_135, c_10428])).
% 7.59/2.86  tff(c_44, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.59/2.86  tff(c_10498, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | r2_hidden('#skF_1', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10464, c_44])).
% 7.59/2.86  tff(c_10598, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_8, c_10498])).
% 7.59/2.86  tff(c_1024, plain, (![C_163, A_164, B_165]: (k2_tarski(k1_funct_1(C_163, A_164), k1_funct_1(C_163, B_165))=k9_relat_1(C_163, k2_tarski(A_164, B_165)) | ~r2_hidden(B_165, k1_relat_1(C_163)) | ~r2_hidden(A_164, k1_relat_1(C_163)) | ~v1_funct_1(C_163) | ~v1_relat_1(C_163))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.59/2.86  tff(c_1034, plain, (![C_163, B_165]: (k9_relat_1(C_163, k2_tarski(B_165, B_165))=k1_tarski(k1_funct_1(C_163, B_165)) | ~r2_hidden(B_165, k1_relat_1(C_163)) | ~r2_hidden(B_165, k1_relat_1(C_163)) | ~v1_funct_1(C_163) | ~v1_relat_1(C_163))), inference(superposition, [status(thm), theory('equality')], [c_1024, c_10])).
% 7.59/2.86  tff(c_1043, plain, (![C_163, B_165]: (k9_relat_1(C_163, k1_tarski(B_165))=k1_tarski(k1_funct_1(C_163, B_165)) | ~r2_hidden(B_165, k1_relat_1(C_163)) | ~r2_hidden(B_165, k1_relat_1(C_163)) | ~v1_funct_1(C_163) | ~v1_relat_1(C_163))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1034])).
% 7.59/2.86  tff(c_10614, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_tarski(k1_funct_1('#skF_2', '#skF_1')) | ~r2_hidden('#skF_1', k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10598, c_1043])).
% 7.59/2.86  tff(c_10617, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_tarski(k1_funct_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_10598, c_10614])).
% 7.59/2.86  tff(c_111, plain, (![B_47, A_48]: (k2_relat_1(k7_relat_1(B_47, A_48))=k9_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.59/2.86  tff(c_117, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_111, c_44])).
% 7.59/2.86  tff(c_123, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_117])).
% 7.59/2.86  tff(c_10756, plain, (~r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10617, c_123])).
% 7.59/2.86  tff(c_10759, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_10756])).
% 7.59/2.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.86  
% 7.59/2.86  Inference rules
% 7.59/2.86  ----------------------
% 7.59/2.86  #Ref     : 0
% 7.59/2.86  #Sup     : 2670
% 7.59/2.86  #Fact    : 4
% 7.59/2.86  #Define  : 0
% 7.59/2.86  #Split   : 6
% 7.59/2.86  #Chain   : 0
% 7.59/2.86  #Close   : 0
% 7.59/2.86  
% 7.59/2.86  Ordering : KBO
% 7.59/2.86  
% 7.59/2.86  Simplification rules
% 7.59/2.86  ----------------------
% 7.59/2.86  #Subsume      : 1153
% 7.59/2.86  #Demod        : 1480
% 7.59/2.86  #Tautology    : 811
% 7.59/2.86  #SimpNegUnit  : 22
% 7.59/2.86  #BackRed      : 5
% 7.59/2.86  
% 7.59/2.86  #Partial instantiations: 0
% 7.59/2.86  #Strategies tried      : 1
% 7.59/2.86  
% 7.59/2.86  Timing (in seconds)
% 7.59/2.86  ----------------------
% 7.59/2.86  Preprocessing        : 0.31
% 7.59/2.86  Parsing              : 0.15
% 7.59/2.86  CNF conversion       : 0.02
% 7.59/2.86  Main loop            : 1.63
% 7.59/2.86  Inferencing          : 0.54
% 7.59/2.86  Reduction            : 0.50
% 7.59/2.86  Demodulation         : 0.36
% 7.59/2.86  BG Simplification    : 0.07
% 7.59/2.86  Subsumption          : 0.43
% 7.59/2.86  Abstraction          : 0.08
% 7.59/2.86  MUC search           : 0.00
% 7.59/2.86  Cooper               : 0.00
% 7.59/2.86  Total                : 1.98
% 7.59/2.86  Index Insertion      : 0.00
% 7.59/2.86  Index Deletion       : 0.00
% 7.59/2.86  Index Matching       : 0.00
% 7.59/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
