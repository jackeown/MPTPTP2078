%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:14 EST 2020

% Result     : Theorem 6.70s
% Output     : CNFRefutation 6.70s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 151 expanded)
%              Number of leaves         :   25 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 342 expanded)
%              Number of equality atoms :    7 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > r1_ordinal1 > v3_ordinal1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_84,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_80,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_98,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ~ ( r2_hidden(A,B)
        & r2_hidden(B,C)
        & r2_hidden(C,D)
        & r2_hidden(D,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_ordinal1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5387,plain,(
    ! [A_316,B_317] :
      ( ~ r2_hidden('#skF_1'(A_316,B_317),B_317)
      | r1_tarski(A_316,B_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5396,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_5387])).

tff(c_50,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    ! [A_28] :
      ( v3_ordinal1(k1_ordinal1(A_28))
      | ~ v3_ordinal1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_48,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5745,plain,(
    ! [B_365,A_366] :
      ( r2_hidden(B_365,A_366)
      | r1_ordinal1(A_366,B_365)
      | ~ v3_ordinal1(B_365)
      | ~ v3_ordinal1(A_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    ! [B_24,A_23] :
      ( B_24 = A_23
      | r2_hidden(A_23,B_24)
      | ~ r2_hidden(A_23,k1_ordinal1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8042,plain,(
    ! [B_492,B_491] :
      ( B_492 = B_491
      | r2_hidden(B_491,B_492)
      | r1_ordinal1(k1_ordinal1(B_492),B_491)
      | ~ v3_ordinal1(B_491)
      | ~ v3_ordinal1(k1_ordinal1(B_492)) ) ),
    inference(resolution,[status(thm)],[c_5745,c_34])).

tff(c_58,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_69,plain,(
    r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_71,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_52])).

tff(c_307,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(A_90,B_91)
      | ~ r1_ordinal1(A_90,B_91)
      | ~ v3_ordinal1(B_91)
      | ~ v3_ordinal1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    ! [B_24] : r2_hidden(B_24,k1_ordinal1(B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_239,plain,(
    ! [C_75,B_76,A_77] :
      ( r2_hidden(C_75,B_76)
      | ~ r2_hidden(C_75,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_248,plain,(
    ! [B_24,B_76] :
      ( r2_hidden(B_24,B_76)
      | ~ r1_tarski(k1_ordinal1(B_24),B_76) ) ),
    inference(resolution,[status(thm)],[c_36,c_239])).

tff(c_5306,plain,(
    ! [B_298,B_299] :
      ( r2_hidden(B_298,B_299)
      | ~ r1_ordinal1(k1_ordinal1(B_298),B_299)
      | ~ v3_ordinal1(B_299)
      | ~ v3_ordinal1(k1_ordinal1(B_298)) ) ),
    inference(resolution,[status(thm)],[c_307,c_248])).

tff(c_5328,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_69,c_5306])).

tff(c_5338,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_5328])).

tff(c_5339,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_5338])).

tff(c_5342,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_5339])).

tff(c_5346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5342])).

tff(c_5347,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_5354,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5347,c_52])).

tff(c_8055,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8042,c_5354])).

tff(c_8066,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_8055])).

tff(c_8132,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_8066])).

tff(c_8135,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_8132])).

tff(c_8139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8135])).

tff(c_8140,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8066])).

tff(c_8142,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8140])).

tff(c_46,plain,(
    ! [B_34,A_33] :
      ( ~ r1_tarski(B_34,A_33)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_5352,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_5347,c_46])).

tff(c_8180,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8142,c_5352])).

tff(c_8186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5396,c_8180])).

tff(c_8187,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_8140])).

tff(c_5510,plain,(
    ! [C_331,B_332,A_333] :
      ( r2_hidden(C_331,B_332)
      | ~ r2_hidden(C_331,A_333)
      | ~ r1_tarski(A_333,B_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5521,plain,(
    ! [B_332] :
      ( r2_hidden('#skF_2',B_332)
      | ~ r1_tarski('#skF_3',B_332) ) ),
    inference(resolution,[status(thm)],[c_5347,c_5510])).

tff(c_6015,plain,(
    ! [D_384,A_385,C_386,B_387] :
      ( ~ r2_hidden(D_384,A_385)
      | ~ r2_hidden(C_386,D_384)
      | ~ r2_hidden(B_387,C_386)
      | ~ r2_hidden(A_385,B_387) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6038,plain,(
    ! [C_386,B_387] :
      ( ~ r2_hidden(C_386,'#skF_2')
      | ~ r2_hidden(B_387,C_386)
      | ~ r2_hidden('#skF_3',B_387) ) ),
    inference(resolution,[status(thm)],[c_5347,c_6015])).

tff(c_8262,plain,(
    ! [B_496] :
      ( ~ r2_hidden(B_496,'#skF_3')
      | ~ r2_hidden('#skF_3',B_496) ) ),
    inference(resolution,[status(thm)],[c_8187,c_6038])).

tff(c_8277,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_5521,c_8262])).

tff(c_8294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5396,c_8187,c_8277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.70/2.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.70/2.49  
% 6.70/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.70/2.49  %$ r2_hidden > r1_xboole_0 > r1_tarski > r1_ordinal1 > v3_ordinal1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.70/2.49  
% 6.70/2.49  %Foreground sorts:
% 6.70/2.49  
% 6.70/2.49  
% 6.70/2.49  %Background operators:
% 6.70/2.49  
% 6.70/2.49  
% 6.70/2.49  %Foreground operators:
% 6.70/2.49  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 6.70/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.70/2.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.70/2.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.70/2.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.70/2.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.70/2.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.70/2.49  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 6.70/2.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.70/2.49  tff('#skF_2', type, '#skF_2': $i).
% 6.70/2.49  tff('#skF_3', type, '#skF_3': $i).
% 6.70/2.49  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 6.70/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.70/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.70/2.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.70/2.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.70/2.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.70/2.49  
% 6.70/2.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.70/2.50  tff(f_108, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 6.70/2.50  tff(f_84, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 6.70/2.50  tff(f_80, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 6.70/2.50  tff(f_71, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 6.70/2.50  tff(f_63, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 6.70/2.50  tff(f_98, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.70/2.50  tff(f_93, axiom, (![A, B, C, D]: ~(((r2_hidden(A, B) & r2_hidden(B, C)) & r2_hidden(C, D)) & r2_hidden(D, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_ordinal1)).
% 6.70/2.50  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.70/2.50  tff(c_5387, plain, (![A_316, B_317]: (~r2_hidden('#skF_1'(A_316, B_317), B_317) | r1_tarski(A_316, B_317))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.70/2.50  tff(c_5396, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_5387])).
% 6.70/2.50  tff(c_50, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.70/2.50  tff(c_42, plain, (![A_28]: (v3_ordinal1(k1_ordinal1(A_28)) | ~v3_ordinal1(A_28))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.70/2.50  tff(c_48, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.70/2.50  tff(c_5745, plain, (![B_365, A_366]: (r2_hidden(B_365, A_366) | r1_ordinal1(A_366, B_365) | ~v3_ordinal1(B_365) | ~v3_ordinal1(A_366))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.70/2.50  tff(c_34, plain, (![B_24, A_23]: (B_24=A_23 | r2_hidden(A_23, B_24) | ~r2_hidden(A_23, k1_ordinal1(B_24)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.70/2.50  tff(c_8042, plain, (![B_492, B_491]: (B_492=B_491 | r2_hidden(B_491, B_492) | r1_ordinal1(k1_ordinal1(B_492), B_491) | ~v3_ordinal1(B_491) | ~v3_ordinal1(k1_ordinal1(B_492)))), inference(resolution, [status(thm)], [c_5745, c_34])).
% 6.70/2.50  tff(c_58, plain, (r2_hidden('#skF_2', '#skF_3') | r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.70/2.50  tff(c_69, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 6.70/2.50  tff(c_52, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.70/2.50  tff(c_71, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_52])).
% 6.70/2.50  tff(c_307, plain, (![A_90, B_91]: (r1_tarski(A_90, B_91) | ~r1_ordinal1(A_90, B_91) | ~v3_ordinal1(B_91) | ~v3_ordinal1(A_90))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.70/2.50  tff(c_36, plain, (![B_24]: (r2_hidden(B_24, k1_ordinal1(B_24)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.70/2.50  tff(c_239, plain, (![C_75, B_76, A_77]: (r2_hidden(C_75, B_76) | ~r2_hidden(C_75, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.70/2.50  tff(c_248, plain, (![B_24, B_76]: (r2_hidden(B_24, B_76) | ~r1_tarski(k1_ordinal1(B_24), B_76))), inference(resolution, [status(thm)], [c_36, c_239])).
% 6.70/2.50  tff(c_5306, plain, (![B_298, B_299]: (r2_hidden(B_298, B_299) | ~r1_ordinal1(k1_ordinal1(B_298), B_299) | ~v3_ordinal1(B_299) | ~v3_ordinal1(k1_ordinal1(B_298)))), inference(resolution, [status(thm)], [c_307, c_248])).
% 6.70/2.50  tff(c_5328, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_69, c_5306])).
% 6.70/2.50  tff(c_5338, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_5328])).
% 6.70/2.50  tff(c_5339, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_71, c_5338])).
% 6.70/2.50  tff(c_5342, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_42, c_5339])).
% 6.70/2.50  tff(c_5346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_5342])).
% 6.70/2.50  tff(c_5347, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 6.70/2.50  tff(c_5354, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5347, c_52])).
% 6.70/2.50  tff(c_8055, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_8042, c_5354])).
% 6.70/2.50  tff(c_8066, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_8055])).
% 6.70/2.50  tff(c_8132, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_8066])).
% 6.70/2.50  tff(c_8135, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_42, c_8132])).
% 6.70/2.50  tff(c_8139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_8135])).
% 6.70/2.50  tff(c_8140, plain, (r2_hidden('#skF_3', '#skF_2') | '#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_8066])).
% 6.70/2.50  tff(c_8142, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_8140])).
% 6.70/2.50  tff(c_46, plain, (![B_34, A_33]: (~r1_tarski(B_34, A_33) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.70/2.50  tff(c_5352, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_5347, c_46])).
% 6.70/2.50  tff(c_8180, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8142, c_5352])).
% 6.70/2.50  tff(c_8186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5396, c_8180])).
% 6.70/2.50  tff(c_8187, plain, (r2_hidden('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_8140])).
% 6.70/2.50  tff(c_5510, plain, (![C_331, B_332, A_333]: (r2_hidden(C_331, B_332) | ~r2_hidden(C_331, A_333) | ~r1_tarski(A_333, B_332))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.70/2.50  tff(c_5521, plain, (![B_332]: (r2_hidden('#skF_2', B_332) | ~r1_tarski('#skF_3', B_332))), inference(resolution, [status(thm)], [c_5347, c_5510])).
% 6.70/2.50  tff(c_6015, plain, (![D_384, A_385, C_386, B_387]: (~r2_hidden(D_384, A_385) | ~r2_hidden(C_386, D_384) | ~r2_hidden(B_387, C_386) | ~r2_hidden(A_385, B_387))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.70/2.50  tff(c_6038, plain, (![C_386, B_387]: (~r2_hidden(C_386, '#skF_2') | ~r2_hidden(B_387, C_386) | ~r2_hidden('#skF_3', B_387))), inference(resolution, [status(thm)], [c_5347, c_6015])).
% 6.70/2.50  tff(c_8262, plain, (![B_496]: (~r2_hidden(B_496, '#skF_3') | ~r2_hidden('#skF_3', B_496))), inference(resolution, [status(thm)], [c_8187, c_6038])).
% 6.70/2.50  tff(c_8277, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_5521, c_8262])).
% 6.70/2.50  tff(c_8294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5396, c_8187, c_8277])).
% 6.70/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.70/2.50  
% 6.70/2.50  Inference rules
% 6.70/2.50  ----------------------
% 6.70/2.50  #Ref     : 0
% 6.70/2.50  #Sup     : 1900
% 6.70/2.50  #Fact    : 4
% 6.70/2.50  #Define  : 0
% 6.70/2.50  #Split   : 8
% 6.70/2.50  #Chain   : 0
% 6.70/2.50  #Close   : 0
% 6.70/2.50  
% 6.70/2.50  Ordering : KBO
% 6.70/2.50  
% 6.70/2.50  Simplification rules
% 6.70/2.50  ----------------------
% 6.70/2.50  #Subsume      : 409
% 6.70/2.50  #Demod        : 397
% 6.70/2.50  #Tautology    : 395
% 6.70/2.50  #SimpNegUnit  : 16
% 6.70/2.50  #BackRed      : 42
% 6.70/2.50  
% 6.70/2.50  #Partial instantiations: 0
% 6.70/2.50  #Strategies tried      : 1
% 6.70/2.50  
% 6.70/2.50  Timing (in seconds)
% 6.70/2.50  ----------------------
% 6.70/2.51  Preprocessing        : 0.31
% 6.70/2.51  Parsing              : 0.18
% 6.70/2.51  CNF conversion       : 0.02
% 7.05/2.51  Main loop            : 1.35
% 7.05/2.51  Inferencing          : 0.46
% 7.05/2.51  Reduction            : 0.39
% 7.05/2.51  Demodulation         : 0.27
% 7.05/2.51  BG Simplification    : 0.06
% 7.05/2.51  Subsumption          : 0.33
% 7.05/2.51  Abstraction          : 0.06
% 7.05/2.51  MUC search           : 0.00
% 7.05/2.51  Cooper               : 0.00
% 7.05/2.51  Total                : 1.70
% 7.05/2.51  Index Insertion      : 0.00
% 7.05/2.51  Index Deletion       : 0.00
% 7.05/2.51  Index Matching       : 0.00
% 7.05/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
