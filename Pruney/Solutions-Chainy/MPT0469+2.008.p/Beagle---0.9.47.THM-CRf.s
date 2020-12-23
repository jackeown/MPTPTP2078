%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:52 EST 2020

% Result     : Theorem 5.97s
% Output     : CNFRefutation 5.97s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 107 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  105 ( 181 expanded)
%              Number of equality atoms :   26 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_56,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
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

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_48,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_57,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_399,plain,(
    ! [A_118,B_119] :
      ( r2_hidden(k4_tarski('#skF_3'(A_118,B_119),'#skF_4'(A_118,B_119)),A_118)
      | r2_hidden('#skF_5'(A_118,B_119),B_119)
      | k1_relat_1(A_118) = B_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_650,plain,(
    ! [A_143,B_144] :
      ( ~ v1_xboole_0(A_143)
      | r2_hidden('#skF_5'(A_143,B_144),B_144)
      | k1_relat_1(A_143) = B_144 ) ),
    inference(resolution,[status(thm)],[c_399,c_2])).

tff(c_676,plain,(
    ! [B_145,A_146] :
      ( ~ v1_xboole_0(B_145)
      | ~ v1_xboole_0(A_146)
      | k1_relat_1(A_146) = B_145 ) ),
    inference(resolution,[status(thm)],[c_650,c_2])).

tff(c_689,plain,(
    ! [A_147] :
      ( ~ v1_xboole_0(A_147)
      | k1_relat_1(A_147) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_676])).

tff(c_701,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_689])).

tff(c_708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_701])).

tff(c_709,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_50,plain,(
    ! [A_41] :
      ( v1_relat_1(A_41)
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_54,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_761,plain,(
    ! [A_160,B_161] :
      ( r2_hidden('#skF_2'(A_160,B_161),B_161)
      | r1_xboole_0(A_160,B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_771,plain,(
    ! [B_164,A_165] :
      ( ~ v1_xboole_0(B_164)
      | r1_xboole_0(A_165,B_164) ) ),
    inference(resolution,[status(thm)],[c_761,c_2])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_781,plain,(
    ! [A_168,B_169] :
      ( k4_xboole_0(A_168,B_169) = A_168
      | ~ v1_xboole_0(B_169) ) ),
    inference(resolution,[status(thm)],[c_771,c_20])).

tff(c_784,plain,(
    ! [A_168] : k4_xboole_0(A_168,k1_xboole_0) = A_168 ),
    inference(resolution,[status(thm)],[c_6,c_781])).

tff(c_38,plain,(
    ! [A_35] :
      ( v1_relat_1(k4_relat_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_710,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_44,plain,(
    ! [A_39] :
      ( k2_relat_1(k4_relat_1(A_39)) = k1_relat_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_835,plain,(
    ! [A_184,B_185] :
      ( r1_tarski(k2_relat_1(A_184),k2_relat_1(B_185))
      | ~ r1_tarski(A_184,B_185)
      | ~ v1_relat_1(B_185)
      | ~ v1_relat_1(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_5964,plain,(
    ! [A_326,A_327] :
      ( r1_tarski(k2_relat_1(A_326),k1_relat_1(A_327))
      | ~ r1_tarski(A_326,k4_relat_1(A_327))
      | ~ v1_relat_1(k4_relat_1(A_327))
      | ~ v1_relat_1(A_326)
      | ~ v1_relat_1(A_327) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_835])).

tff(c_6003,plain,(
    ! [A_326] :
      ( r1_tarski(k2_relat_1(A_326),k1_xboole_0)
      | ~ r1_tarski(A_326,k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(A_326)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_5964])).

tff(c_6006,plain,(
    ! [A_326] :
      ( r1_tarski(k2_relat_1(A_326),k1_xboole_0)
      | ~ r1_tarski(A_326,k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(A_326) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6003])).

tff(c_6202,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_6006])).

tff(c_6205,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_6202])).

tff(c_6209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6205])).

tff(c_6596,plain,(
    ! [A_334] :
      ( r1_tarski(k2_relat_1(A_334),k1_xboole_0)
      | ~ r1_tarski(A_334,k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(A_334) ) ),
    inference(splitRight,[status(thm)],[c_6006])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6602,plain,(
    ! [A_334] :
      ( k4_xboole_0(k2_relat_1(A_334),k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(A_334,k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(A_334) ) ),
    inference(resolution,[status(thm)],[c_6596,c_16])).

tff(c_6609,plain,(
    ! [A_335] :
      ( k2_relat_1(A_335) = k1_xboole_0
      | ~ r1_tarski(A_335,k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(A_335) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_6602])).

tff(c_6617,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_6609])).

tff(c_6621,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6617])).

tff(c_6623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_709,c_6621])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:41:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.97/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.14  
% 5.97/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.14  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 5.97/2.14  
% 5.97/2.14  %Foreground sorts:
% 5.97/2.14  
% 5.97/2.14  
% 5.97/2.14  %Background operators:
% 5.97/2.14  
% 5.97/2.14  
% 5.97/2.14  %Foreground operators:
% 5.97/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.97/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.97/2.14  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.97/2.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.97/2.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.97/2.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.97/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.97/2.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.97/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.97/2.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.97/2.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.97/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.97/2.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.97/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.97/2.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.97/2.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.97/2.14  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.97/2.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.97/2.14  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.97/2.14  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.97/2.14  
% 5.97/2.15  tff(f_97, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.97/2.15  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.97/2.15  tff(f_72, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 5.97/2.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.97/2.15  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 5.97/2.15  tff(f_56, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.97/2.15  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.97/2.15  tff(f_60, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.97/2.15  tff(f_76, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 5.97/2.15  tff(f_93, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 5.97/2.15  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 5.97/2.15  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.97/2.15  tff(c_48, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.97/2.15  tff(c_57, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 5.97/2.15  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.97/2.15  tff(c_399, plain, (![A_118, B_119]: (r2_hidden(k4_tarski('#skF_3'(A_118, B_119), '#skF_4'(A_118, B_119)), A_118) | r2_hidden('#skF_5'(A_118, B_119), B_119) | k1_relat_1(A_118)=B_119)), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.97/2.15  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.97/2.15  tff(c_650, plain, (![A_143, B_144]: (~v1_xboole_0(A_143) | r2_hidden('#skF_5'(A_143, B_144), B_144) | k1_relat_1(A_143)=B_144)), inference(resolution, [status(thm)], [c_399, c_2])).
% 5.97/2.15  tff(c_676, plain, (![B_145, A_146]: (~v1_xboole_0(B_145) | ~v1_xboole_0(A_146) | k1_relat_1(A_146)=B_145)), inference(resolution, [status(thm)], [c_650, c_2])).
% 5.97/2.15  tff(c_689, plain, (![A_147]: (~v1_xboole_0(A_147) | k1_relat_1(A_147)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_676])).
% 5.97/2.15  tff(c_701, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_689])).
% 5.97/2.15  tff(c_708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_701])).
% 5.97/2.15  tff(c_709, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 5.97/2.15  tff(c_50, plain, (![A_41]: (v1_relat_1(A_41) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.97/2.15  tff(c_54, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_50])).
% 5.97/2.15  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.97/2.15  tff(c_761, plain, (![A_160, B_161]: (r2_hidden('#skF_2'(A_160, B_161), B_161) | r1_xboole_0(A_160, B_161))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.97/2.15  tff(c_771, plain, (![B_164, A_165]: (~v1_xboole_0(B_164) | r1_xboole_0(A_165, B_164))), inference(resolution, [status(thm)], [c_761, c_2])).
% 5.97/2.16  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.97/2.16  tff(c_781, plain, (![A_168, B_169]: (k4_xboole_0(A_168, B_169)=A_168 | ~v1_xboole_0(B_169))), inference(resolution, [status(thm)], [c_771, c_20])).
% 5.97/2.16  tff(c_784, plain, (![A_168]: (k4_xboole_0(A_168, k1_xboole_0)=A_168)), inference(resolution, [status(thm)], [c_6, c_781])).
% 5.97/2.16  tff(c_38, plain, (![A_35]: (v1_relat_1(k4_relat_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.97/2.16  tff(c_710, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 5.97/2.16  tff(c_44, plain, (![A_39]: (k2_relat_1(k4_relat_1(A_39))=k1_relat_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.97/2.16  tff(c_835, plain, (![A_184, B_185]: (r1_tarski(k2_relat_1(A_184), k2_relat_1(B_185)) | ~r1_tarski(A_184, B_185) | ~v1_relat_1(B_185) | ~v1_relat_1(A_184))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.97/2.16  tff(c_5964, plain, (![A_326, A_327]: (r1_tarski(k2_relat_1(A_326), k1_relat_1(A_327)) | ~r1_tarski(A_326, k4_relat_1(A_327)) | ~v1_relat_1(k4_relat_1(A_327)) | ~v1_relat_1(A_326) | ~v1_relat_1(A_327))), inference(superposition, [status(thm), theory('equality')], [c_44, c_835])).
% 5.97/2.16  tff(c_6003, plain, (![A_326]: (r1_tarski(k2_relat_1(A_326), k1_xboole_0) | ~r1_tarski(A_326, k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(A_326) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_710, c_5964])).
% 5.97/2.16  tff(c_6006, plain, (![A_326]: (r1_tarski(k2_relat_1(A_326), k1_xboole_0) | ~r1_tarski(A_326, k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(A_326))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6003])).
% 5.97/2.16  tff(c_6202, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_6006])).
% 5.97/2.16  tff(c_6205, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_6202])).
% 5.97/2.16  tff(c_6209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_6205])).
% 5.97/2.16  tff(c_6596, plain, (![A_334]: (r1_tarski(k2_relat_1(A_334), k1_xboole_0) | ~r1_tarski(A_334, k4_relat_1(k1_xboole_0)) | ~v1_relat_1(A_334))), inference(splitRight, [status(thm)], [c_6006])).
% 5.97/2.16  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.97/2.16  tff(c_6602, plain, (![A_334]: (k4_xboole_0(k2_relat_1(A_334), k1_xboole_0)=k1_xboole_0 | ~r1_tarski(A_334, k4_relat_1(k1_xboole_0)) | ~v1_relat_1(A_334))), inference(resolution, [status(thm)], [c_6596, c_16])).
% 5.97/2.16  tff(c_6609, plain, (![A_335]: (k2_relat_1(A_335)=k1_xboole_0 | ~r1_tarski(A_335, k4_relat_1(k1_xboole_0)) | ~v1_relat_1(A_335))), inference(demodulation, [status(thm), theory('equality')], [c_784, c_6602])).
% 5.97/2.16  tff(c_6617, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_6609])).
% 5.97/2.16  tff(c_6621, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6617])).
% 5.97/2.16  tff(c_6623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_709, c_6621])).
% 5.97/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.16  
% 5.97/2.16  Inference rules
% 5.97/2.16  ----------------------
% 5.97/2.16  #Ref     : 0
% 5.97/2.16  #Sup     : 1678
% 5.97/2.16  #Fact    : 0
% 5.97/2.16  #Define  : 0
% 5.97/2.16  #Split   : 3
% 5.97/2.16  #Chain   : 0
% 5.97/2.16  #Close   : 0
% 5.97/2.16  
% 5.97/2.16  Ordering : KBO
% 5.97/2.16  
% 5.97/2.16  Simplification rules
% 5.97/2.16  ----------------------
% 5.97/2.16  #Subsume      : 435
% 5.97/2.16  #Demod        : 1490
% 5.97/2.16  #Tautology    : 708
% 5.97/2.16  #SimpNegUnit  : 13
% 5.97/2.16  #BackRed      : 0
% 5.97/2.16  
% 5.97/2.16  #Partial instantiations: 0
% 5.97/2.16  #Strategies tried      : 1
% 5.97/2.16  
% 5.97/2.16  Timing (in seconds)
% 5.97/2.16  ----------------------
% 5.97/2.16  Preprocessing        : 0.29
% 5.97/2.16  Parsing              : 0.16
% 5.97/2.16  CNF conversion       : 0.02
% 5.97/2.16  Main loop            : 1.11
% 5.97/2.16  Inferencing          : 0.36
% 5.97/2.16  Reduction            : 0.28
% 5.97/2.16  Demodulation         : 0.19
% 5.97/2.16  BG Simplification    : 0.04
% 5.97/2.16  Subsumption          : 0.36
% 5.97/2.16  Abstraction          : 0.05
% 5.97/2.16  MUC search           : 0.00
% 5.97/2.16  Cooper               : 0.00
% 5.97/2.16  Total                : 1.44
% 5.97/2.16  Index Insertion      : 0.00
% 5.97/2.16  Index Deletion       : 0.00
% 5.97/2.16  Index Matching       : 0.00
% 5.97/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
