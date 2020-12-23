%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:33 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 126 expanded)
%              Number of leaves         :   32 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  121 ( 256 expanded)
%              Number of equality atoms :   28 (  59 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_66,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k7_relat_1(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_305,plain,(
    ! [A_69,C_70,B_71] :
      ( r1_xboole_0(k2_tarski(A_69,C_70),B_71)
      | r2_hidden(C_70,B_71)
      | r2_hidden(A_69,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_308,plain,(
    ! [A_4,B_71] :
      ( r1_xboole_0(k1_tarski(A_4),B_71)
      | r2_hidden(A_4,B_71)
      | r2_hidden(A_4,B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_305])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_386,plain,(
    ! [C_80,A_81,B_82] :
      ( k7_relat_1(k7_relat_1(C_80,A_81),B_82) = k1_xboole_0
      | ~ r1_xboole_0(A_81,B_82)
      | ~ v1_relat_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( k2_relat_1(k7_relat_1(B_16,A_15)) = k9_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_402,plain,(
    ! [C_80,A_81,B_82] :
      ( k9_relat_1(k7_relat_1(C_80,A_81),B_82) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k7_relat_1(C_80,A_81))
      | ~ r1_xboole_0(A_81,B_82)
      | ~ v1_relat_1(C_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_20])).

tff(c_472,plain,(
    ! [C_93,A_94,B_95] :
      ( k9_relat_1(k7_relat_1(C_93,A_94),B_95) = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1(C_93,A_94))
      | ~ r1_xboole_0(A_94,B_95)
      | ~ v1_relat_1(C_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_402])).

tff(c_486,plain,(
    ! [A_96,B_97,B_98] :
      ( k9_relat_1(k7_relat_1(A_96,B_97),B_98) = k1_xboole_0
      | ~ r1_xboole_0(B_97,B_98)
      | ~ v1_relat_1(A_96) ) ),
    inference(resolution,[status(thm)],[c_18,c_472])).

tff(c_119,plain,(
    ! [B_43,A_44] :
      ( k7_relat_1(B_43,A_44) = B_43
      | ~ r1_tarski(k1_relat_1(B_43),A_44)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_316,plain,(
    ! [B_73] :
      ( k7_relat_1(B_73,k1_relat_1(B_73)) = B_73
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_6,c_119])).

tff(c_326,plain,(
    ! [B_73] :
      ( k9_relat_1(B_73,k1_relat_1(B_73)) = k2_relat_1(B_73)
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_20])).

tff(c_1045,plain,(
    ! [A_143,B_144] :
      ( k2_relat_1(k7_relat_1(A_143,B_144)) = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1(A_143,B_144))
      | ~ v1_relat_1(k7_relat_1(A_143,B_144))
      | ~ r1_xboole_0(B_144,k1_relat_1(k7_relat_1(A_143,B_144)))
      | ~ v1_relat_1(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_326])).

tff(c_1085,plain,(
    ! [A_145,A_146] :
      ( k2_relat_1(k7_relat_1(A_145,k1_tarski(A_146))) = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1(A_145,k1_tarski(A_146)))
      | ~ v1_relat_1(A_145)
      | r2_hidden(A_146,k1_relat_1(k7_relat_1(A_145,k1_tarski(A_146)))) ) ),
    inference(resolution,[status(thm)],[c_308,c_1045])).

tff(c_30,plain,(
    ! [A_20,C_22,B_21] :
      ( r2_hidden(A_20,k1_relat_1(C_22))
      | ~ r2_hidden(A_20,k1_relat_1(k7_relat_1(C_22,B_21)))
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1126,plain,(
    ! [A_147,A_148] :
      ( r2_hidden(A_147,k1_relat_1(A_148))
      | k2_relat_1(k7_relat_1(A_148,k1_tarski(A_147))) = k1_xboole_0
      | ~ v1_relat_1(k7_relat_1(A_148,k1_tarski(A_147)))
      | ~ v1_relat_1(A_148) ) ),
    inference(resolution,[status(thm)],[c_1085,c_30])).

tff(c_1159,plain,(
    ! [A_149,A_150] :
      ( r2_hidden(A_149,k1_relat_1(A_150))
      | k2_relat_1(k7_relat_1(A_150,k1_tarski(A_149))) = k1_xboole_0
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_18,c_1126])).

tff(c_38,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1168,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1159,c_38])).

tff(c_1195,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8,c_1168])).

tff(c_544,plain,(
    ! [C_103,A_104,B_105] :
      ( k2_tarski(k1_funct_1(C_103,A_104),k1_funct_1(C_103,B_105)) = k9_relat_1(C_103,k2_tarski(A_104,B_105))
      | ~ r2_hidden(B_105,k1_relat_1(C_103))
      | ~ r2_hidden(A_104,k1_relat_1(C_103))
      | ~ v1_funct_1(C_103)
      | ~ v1_relat_1(C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_554,plain,(
    ! [C_103,B_105] :
      ( k9_relat_1(C_103,k2_tarski(B_105,B_105)) = k1_tarski(k1_funct_1(C_103,B_105))
      | ~ r2_hidden(B_105,k1_relat_1(C_103))
      | ~ r2_hidden(B_105,k1_relat_1(C_103))
      | ~ v1_funct_1(C_103)
      | ~ v1_relat_1(C_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_544,c_10])).

tff(c_563,plain,(
    ! [C_103,B_105] :
      ( k9_relat_1(C_103,k1_tarski(B_105)) = k1_tarski(k1_funct_1(C_103,B_105))
      | ~ r2_hidden(B_105,k1_relat_1(C_103))
      | ~ r2_hidden(B_105,k1_relat_1(C_103))
      | ~ v1_funct_1(C_103)
      | ~ v1_relat_1(C_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_554])).

tff(c_1206,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_tarski(k1_funct_1('#skF_2','#skF_1'))
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1195,c_563])).

tff(c_1212,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_tarski(k1_funct_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1195,c_1206])).

tff(c_96,plain,(
    ! [B_38,A_39] :
      ( k2_relat_1(k7_relat_1(B_38,A_39)) = k9_relat_1(B_38,A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_102,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_38])).

tff(c_108,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_102])).

tff(c_1213,plain,(
    ~ r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1212,c_108])).

tff(c_1216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.51  
% 2.99/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.51  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.99/1.51  
% 2.99/1.51  %Foreground sorts:
% 2.99/1.51  
% 2.99/1.51  
% 2.99/1.51  %Background operators:
% 2.99/1.51  
% 2.99/1.51  
% 2.99/1.51  %Foreground operators:
% 2.99/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.99/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.99/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.99/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.99/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.99/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.99/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.99/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.99/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.99/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.99/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.99/1.51  
% 2.99/1.53  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.99/1.53  tff(f_97, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_funct_1)).
% 2.99/1.53  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.99/1.53  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.99/1.53  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.99/1.53  tff(f_49, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 2.99/1.53  tff(f_66, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.99/1.53  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 2.99/1.53  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.99/1.53  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.99/1.53  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 2.99/1.53  tff(f_90, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 2.99/1.53  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.99/1.53  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.99/1.53  tff(c_40, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.99/1.53  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.99/1.53  tff(c_18, plain, (![A_13, B_14]: (v1_relat_1(k7_relat_1(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.99/1.53  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.99/1.53  tff(c_305, plain, (![A_69, C_70, B_71]: (r1_xboole_0(k2_tarski(A_69, C_70), B_71) | r2_hidden(C_70, B_71) | r2_hidden(A_69, B_71))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.99/1.53  tff(c_308, plain, (![A_4, B_71]: (r1_xboole_0(k1_tarski(A_4), B_71) | r2_hidden(A_4, B_71) | r2_hidden(A_4, B_71))), inference(superposition, [status(thm), theory('equality')], [c_10, c_305])).
% 2.99/1.53  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.99/1.53  tff(c_386, plain, (![C_80, A_81, B_82]: (k7_relat_1(k7_relat_1(C_80, A_81), B_82)=k1_xboole_0 | ~r1_xboole_0(A_81, B_82) | ~v1_relat_1(C_80))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.99/1.53  tff(c_20, plain, (![B_16, A_15]: (k2_relat_1(k7_relat_1(B_16, A_15))=k9_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.99/1.53  tff(c_402, plain, (![C_80, A_81, B_82]: (k9_relat_1(k7_relat_1(C_80, A_81), B_82)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k7_relat_1(C_80, A_81)) | ~r1_xboole_0(A_81, B_82) | ~v1_relat_1(C_80))), inference(superposition, [status(thm), theory('equality')], [c_386, c_20])).
% 2.99/1.53  tff(c_472, plain, (![C_93, A_94, B_95]: (k9_relat_1(k7_relat_1(C_93, A_94), B_95)=k1_xboole_0 | ~v1_relat_1(k7_relat_1(C_93, A_94)) | ~r1_xboole_0(A_94, B_95) | ~v1_relat_1(C_93))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_402])).
% 2.99/1.53  tff(c_486, plain, (![A_96, B_97, B_98]: (k9_relat_1(k7_relat_1(A_96, B_97), B_98)=k1_xboole_0 | ~r1_xboole_0(B_97, B_98) | ~v1_relat_1(A_96))), inference(resolution, [status(thm)], [c_18, c_472])).
% 2.99/1.53  tff(c_119, plain, (![B_43, A_44]: (k7_relat_1(B_43, A_44)=B_43 | ~r1_tarski(k1_relat_1(B_43), A_44) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.99/1.53  tff(c_316, plain, (![B_73]: (k7_relat_1(B_73, k1_relat_1(B_73))=B_73 | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_6, c_119])).
% 2.99/1.53  tff(c_326, plain, (![B_73]: (k9_relat_1(B_73, k1_relat_1(B_73))=k2_relat_1(B_73) | ~v1_relat_1(B_73) | ~v1_relat_1(B_73))), inference(superposition, [status(thm), theory('equality')], [c_316, c_20])).
% 2.99/1.53  tff(c_1045, plain, (![A_143, B_144]: (k2_relat_1(k7_relat_1(A_143, B_144))=k1_xboole_0 | ~v1_relat_1(k7_relat_1(A_143, B_144)) | ~v1_relat_1(k7_relat_1(A_143, B_144)) | ~r1_xboole_0(B_144, k1_relat_1(k7_relat_1(A_143, B_144))) | ~v1_relat_1(A_143))), inference(superposition, [status(thm), theory('equality')], [c_486, c_326])).
% 2.99/1.53  tff(c_1085, plain, (![A_145, A_146]: (k2_relat_1(k7_relat_1(A_145, k1_tarski(A_146)))=k1_xboole_0 | ~v1_relat_1(k7_relat_1(A_145, k1_tarski(A_146))) | ~v1_relat_1(A_145) | r2_hidden(A_146, k1_relat_1(k7_relat_1(A_145, k1_tarski(A_146)))))), inference(resolution, [status(thm)], [c_308, c_1045])).
% 2.99/1.53  tff(c_30, plain, (![A_20, C_22, B_21]: (r2_hidden(A_20, k1_relat_1(C_22)) | ~r2_hidden(A_20, k1_relat_1(k7_relat_1(C_22, B_21))) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.99/1.53  tff(c_1126, plain, (![A_147, A_148]: (r2_hidden(A_147, k1_relat_1(A_148)) | k2_relat_1(k7_relat_1(A_148, k1_tarski(A_147)))=k1_xboole_0 | ~v1_relat_1(k7_relat_1(A_148, k1_tarski(A_147))) | ~v1_relat_1(A_148))), inference(resolution, [status(thm)], [c_1085, c_30])).
% 2.99/1.53  tff(c_1159, plain, (![A_149, A_150]: (r2_hidden(A_149, k1_relat_1(A_150)) | k2_relat_1(k7_relat_1(A_150, k1_tarski(A_149)))=k1_xboole_0 | ~v1_relat_1(A_150))), inference(resolution, [status(thm)], [c_18, c_1126])).
% 2.99/1.53  tff(c_38, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.99/1.53  tff(c_1168, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | r2_hidden('#skF_1', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1159, c_38])).
% 2.99/1.53  tff(c_1195, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8, c_1168])).
% 2.99/1.53  tff(c_544, plain, (![C_103, A_104, B_105]: (k2_tarski(k1_funct_1(C_103, A_104), k1_funct_1(C_103, B_105))=k9_relat_1(C_103, k2_tarski(A_104, B_105)) | ~r2_hidden(B_105, k1_relat_1(C_103)) | ~r2_hidden(A_104, k1_relat_1(C_103)) | ~v1_funct_1(C_103) | ~v1_relat_1(C_103))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.99/1.53  tff(c_554, plain, (![C_103, B_105]: (k9_relat_1(C_103, k2_tarski(B_105, B_105))=k1_tarski(k1_funct_1(C_103, B_105)) | ~r2_hidden(B_105, k1_relat_1(C_103)) | ~r2_hidden(B_105, k1_relat_1(C_103)) | ~v1_funct_1(C_103) | ~v1_relat_1(C_103))), inference(superposition, [status(thm), theory('equality')], [c_544, c_10])).
% 2.99/1.53  tff(c_563, plain, (![C_103, B_105]: (k9_relat_1(C_103, k1_tarski(B_105))=k1_tarski(k1_funct_1(C_103, B_105)) | ~r2_hidden(B_105, k1_relat_1(C_103)) | ~r2_hidden(B_105, k1_relat_1(C_103)) | ~v1_funct_1(C_103) | ~v1_relat_1(C_103))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_554])).
% 2.99/1.53  tff(c_1206, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_tarski(k1_funct_1('#skF_2', '#skF_1')) | ~r2_hidden('#skF_1', k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1195, c_563])).
% 2.99/1.53  tff(c_1212, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_tarski(k1_funct_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1195, c_1206])).
% 2.99/1.53  tff(c_96, plain, (![B_38, A_39]: (k2_relat_1(k7_relat_1(B_38, A_39))=k9_relat_1(B_38, A_39) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.99/1.53  tff(c_102, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_96, c_38])).
% 2.99/1.53  tff(c_108, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_102])).
% 2.99/1.53  tff(c_1213, plain, (~r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1212, c_108])).
% 2.99/1.53  tff(c_1216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1213])).
% 2.99/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.53  
% 2.99/1.53  Inference rules
% 2.99/1.53  ----------------------
% 2.99/1.53  #Ref     : 0
% 2.99/1.53  #Sup     : 261
% 2.99/1.53  #Fact    : 2
% 2.99/1.53  #Define  : 0
% 2.99/1.53  #Split   : 3
% 2.99/1.53  #Chain   : 0
% 2.99/1.53  #Close   : 0
% 2.99/1.53  
% 2.99/1.53  Ordering : KBO
% 2.99/1.53  
% 2.99/1.53  Simplification rules
% 2.99/1.53  ----------------------
% 2.99/1.53  #Subsume      : 54
% 2.99/1.53  #Demod        : 219
% 3.31/1.53  #Tautology    : 139
% 3.31/1.53  #SimpNegUnit  : 4
% 3.31/1.53  #BackRed      : 2
% 3.31/1.53  
% 3.31/1.53  #Partial instantiations: 0
% 3.31/1.53  #Strategies tried      : 1
% 3.31/1.53  
% 3.31/1.53  Timing (in seconds)
% 3.31/1.53  ----------------------
% 3.31/1.53  Preprocessing        : 0.31
% 3.31/1.53  Parsing              : 0.15
% 3.31/1.53  CNF conversion       : 0.02
% 3.31/1.53  Main loop            : 0.43
% 3.31/1.53  Inferencing          : 0.16
% 3.31/1.53  Reduction            : 0.13
% 3.31/1.53  Demodulation         : 0.09
% 3.31/1.53  BG Simplification    : 0.02
% 3.31/1.53  Subsumption          : 0.09
% 3.31/1.53  Abstraction          : 0.03
% 3.31/1.53  MUC search           : 0.00
% 3.31/1.53  Cooper               : 0.00
% 3.31/1.53  Total                : 0.77
% 3.31/1.53  Index Insertion      : 0.00
% 3.31/1.53  Index Deletion       : 0.00
% 3.31/1.53  Index Matching       : 0.00
% 3.31/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
