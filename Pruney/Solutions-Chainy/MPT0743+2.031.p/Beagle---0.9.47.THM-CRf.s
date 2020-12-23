%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:12 EST 2020

% Result     : Theorem 4.95s
% Output     : CNFRefutation 5.27s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 151 expanded)
%              Number of leaves         :   22 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  130 ( 342 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_75,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_71,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_34,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2541,plain,(
    ! [A_211,B_212] :
      ( r1_tarski(A_211,B_212)
      | ~ r1_ordinal1(A_211,B_212)
      | ~ v3_ordinal1(B_212)
      | ~ v3_ordinal1(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_64,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_30,plain,(
    ! [A_18] :
      ( v3_ordinal1(k1_ordinal1(A_18))
      | ~ v3_ordinal1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_44,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_65,plain,(
    r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_191,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ r1_ordinal1(A_59,B_60)
      | ~ v3_ordinal1(B_60)
      | ~ v3_ordinal1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    ! [B_14] : r2_hidden(B_14,k1_ordinal1(B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_132,plain,(
    ! [C_46,B_47,A_48] :
      ( r2_hidden(C_46,B_47)
      | ~ r2_hidden(C_46,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_141,plain,(
    ! [B_14,B_47] :
      ( r2_hidden(B_14,B_47)
      | ~ r1_tarski(k1_ordinal1(B_14),B_47) ) ),
    inference(resolution,[status(thm)],[c_24,c_132])).

tff(c_2352,plain,(
    ! [B_183,B_184] :
      ( r2_hidden(B_183,B_184)
      | ~ r1_ordinal1(k1_ordinal1(B_183),B_184)
      | ~ v3_ordinal1(B_184)
      | ~ v3_ordinal1(k1_ordinal1(B_183)) ) ),
    inference(resolution,[status(thm)],[c_191,c_141])).

tff(c_2382,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_65,c_2352])).

tff(c_2395,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2382])).

tff(c_2396,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2395])).

tff(c_2399,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_2396])).

tff(c_2403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2399])).

tff(c_2404,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2404])).

tff(c_2408,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_32,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2420,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_2408,c_32])).

tff(c_2561,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2541,c_2420])).

tff(c_2575,plain,(
    ~ r1_ordinal1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_2561])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( r1_ordinal1(B_9,A_8)
      | r1_ordinal1(A_8,B_9)
      | ~ v3_ordinal1(B_9)
      | ~ v3_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ r1_ordinal1(A_11,B_12)
      | ~ v3_ordinal1(B_12)
      | ~ v3_ordinal1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2677,plain,(
    ! [B_223,A_224] :
      ( r1_ordinal1(B_223,A_224)
      | r1_ordinal1(A_224,B_223)
      | ~ v3_ordinal1(B_223)
      | ~ v3_ordinal1(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2407,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2688,plain,
    ( r1_ordinal1('#skF_3',k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2677,c_2407])).

tff(c_2706,plain,
    ( r1_ordinal1('#skF_3',k1_ordinal1('#skF_2'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2688])).

tff(c_2721,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2706])).

tff(c_2725,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_2721])).

tff(c_2729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2725])).

tff(c_2731,plain,(
    v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2706])).

tff(c_2614,plain,(
    ! [B_220,A_221] :
      ( r2_hidden(B_220,A_221)
      | r1_ordinal1(A_221,B_220)
      | ~ v3_ordinal1(B_220)
      | ~ v3_ordinal1(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( B_14 = A_13
      | r2_hidden(A_13,B_14)
      | ~ r2_hidden(A_13,k1_ordinal1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3625,plain,(
    ! [B_293,B_292] :
      ( B_293 = B_292
      | r2_hidden(B_292,B_293)
      | r1_ordinal1(k1_ordinal1(B_293),B_292)
      | ~ v3_ordinal1(B_292)
      | ~ v3_ordinal1(k1_ordinal1(B_293)) ) ),
    inference(resolution,[status(thm)],[c_2614,c_22])).

tff(c_3642,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3625,c_2407])).

tff(c_3656,plain,
    ( '#skF_2' = '#skF_3'
    | r2_hidden('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2731,c_34,c_3642])).

tff(c_3657,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3656])).

tff(c_3664,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_3657,c_32])).

tff(c_3667,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_3664])).

tff(c_3670,plain,(
    ~ r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_3667])).

tff(c_3689,plain,
    ( r1_ordinal1('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_3670])).

tff(c_3698,plain,(
    r1_ordinal1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_3689])).

tff(c_3700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2575,c_3698])).

tff(c_3701,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3656])).

tff(c_3740,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3701,c_2420])).

tff(c_3749,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3740])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:45:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.95/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.27/1.99  
% 5.27/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.27/1.99  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_1
% 5.27/1.99  
% 5.27/1.99  %Foreground sorts:
% 5.27/1.99  
% 5.27/1.99  
% 5.27/1.99  %Background operators:
% 5.27/1.99  
% 5.27/1.99  
% 5.27/1.99  %Foreground operators:
% 5.27/1.99  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 5.27/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.27/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.27/1.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.27/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.27/1.99  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 5.27/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.27/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.27/1.99  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 5.27/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.27/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.27/1.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.27/1.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.27/1.99  
% 5.27/2.00  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.27/2.00  tff(f_90, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 5.27/2.00  tff(f_56, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 5.27/2.00  tff(f_75, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 5.27/2.00  tff(f_62, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 5.27/2.00  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.27/2.00  tff(f_80, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.27/2.00  tff(f_46, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 5.27/2.00  tff(f_71, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 5.27/2.00  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.27/2.00  tff(c_34, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.27/2.00  tff(c_36, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.27/2.00  tff(c_2541, plain, (![A_211, B_212]: (r1_tarski(A_211, B_212) | ~r1_ordinal1(A_211, B_212) | ~v3_ordinal1(B_212) | ~v3_ordinal1(A_211))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.27/2.00  tff(c_38, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3') | ~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.27/2.00  tff(c_64, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 5.27/2.00  tff(c_30, plain, (![A_18]: (v3_ordinal1(k1_ordinal1(A_18)) | ~v3_ordinal1(A_18))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.27/2.00  tff(c_44, plain, (r2_hidden('#skF_2', '#skF_3') | r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.27/2.00  tff(c_65, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 5.27/2.00  tff(c_191, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~r1_ordinal1(A_59, B_60) | ~v3_ordinal1(B_60) | ~v3_ordinal1(A_59))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.27/2.00  tff(c_24, plain, (![B_14]: (r2_hidden(B_14, k1_ordinal1(B_14)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.27/2.00  tff(c_132, plain, (![C_46, B_47, A_48]: (r2_hidden(C_46, B_47) | ~r2_hidden(C_46, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.27/2.00  tff(c_141, plain, (![B_14, B_47]: (r2_hidden(B_14, B_47) | ~r1_tarski(k1_ordinal1(B_14), B_47))), inference(resolution, [status(thm)], [c_24, c_132])).
% 5.27/2.00  tff(c_2352, plain, (![B_183, B_184]: (r2_hidden(B_183, B_184) | ~r1_ordinal1(k1_ordinal1(B_183), B_184) | ~v3_ordinal1(B_184) | ~v3_ordinal1(k1_ordinal1(B_183)))), inference(resolution, [status(thm)], [c_191, c_141])).
% 5.27/2.00  tff(c_2382, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_65, c_2352])).
% 5.27/2.00  tff(c_2395, plain, (r2_hidden('#skF_2', '#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2382])).
% 5.27/2.00  tff(c_2396, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_2395])).
% 5.27/2.00  tff(c_2399, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_2396])).
% 5.27/2.00  tff(c_2403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_2399])).
% 5.27/2.00  tff(c_2404, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 5.27/2.00  tff(c_2406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2404])).
% 5.27/2.00  tff(c_2408, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 5.27/2.00  tff(c_32, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.27/2.00  tff(c_2420, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_2408, c_32])).
% 5.27/2.00  tff(c_2561, plain, (~r1_ordinal1('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_2541, c_2420])).
% 5.27/2.00  tff(c_2575, plain, (~r1_ordinal1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_2561])).
% 5.27/2.00  tff(c_14, plain, (![B_9, A_8]: (r1_ordinal1(B_9, A_8) | r1_ordinal1(A_8, B_9) | ~v3_ordinal1(B_9) | ~v3_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.27/2.00  tff(c_20, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~r1_ordinal1(A_11, B_12) | ~v3_ordinal1(B_12) | ~v3_ordinal1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.27/2.00  tff(c_2677, plain, (![B_223, A_224]: (r1_ordinal1(B_223, A_224) | r1_ordinal1(A_224, B_223) | ~v3_ordinal1(B_223) | ~v3_ordinal1(A_224))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.27/2.00  tff(c_2407, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 5.27/2.00  tff(c_2688, plain, (r1_ordinal1('#skF_3', k1_ordinal1('#skF_2')) | ~v3_ordinal1(k1_ordinal1('#skF_2')) | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_2677, c_2407])).
% 5.27/2.00  tff(c_2706, plain, (r1_ordinal1('#skF_3', k1_ordinal1('#skF_2')) | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2688])).
% 5.27/2.00  tff(c_2721, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_2706])).
% 5.27/2.00  tff(c_2725, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_2721])).
% 5.27/2.00  tff(c_2729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_2725])).
% 5.27/2.00  tff(c_2731, plain, (v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitRight, [status(thm)], [c_2706])).
% 5.27/2.00  tff(c_2614, plain, (![B_220, A_221]: (r2_hidden(B_220, A_221) | r1_ordinal1(A_221, B_220) | ~v3_ordinal1(B_220) | ~v3_ordinal1(A_221))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.27/2.00  tff(c_22, plain, (![B_14, A_13]: (B_14=A_13 | r2_hidden(A_13, B_14) | ~r2_hidden(A_13, k1_ordinal1(B_14)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.27/2.00  tff(c_3625, plain, (![B_293, B_292]: (B_293=B_292 | r2_hidden(B_292, B_293) | r1_ordinal1(k1_ordinal1(B_293), B_292) | ~v3_ordinal1(B_292) | ~v3_ordinal1(k1_ordinal1(B_293)))), inference(resolution, [status(thm)], [c_2614, c_22])).
% 5.27/2.00  tff(c_3642, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_3625, c_2407])).
% 5.27/2.00  tff(c_3656, plain, ('#skF_2'='#skF_3' | r2_hidden('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2731, c_34, c_3642])).
% 5.27/2.00  tff(c_3657, plain, (r2_hidden('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_3656])).
% 5.27/2.00  tff(c_3664, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_3657, c_32])).
% 5.27/2.00  tff(c_3667, plain, (~r1_ordinal1('#skF_2', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_3664])).
% 5.27/2.00  tff(c_3670, plain, (~r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_3667])).
% 5.27/2.00  tff(c_3689, plain, (r1_ordinal1('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_3670])).
% 5.27/2.00  tff(c_3698, plain, (r1_ordinal1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_3689])).
% 5.27/2.00  tff(c_3700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2575, c_3698])).
% 5.27/2.00  tff(c_3701, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_3656])).
% 5.27/2.00  tff(c_3740, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3701, c_2420])).
% 5.27/2.00  tff(c_3749, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_3740])).
% 5.27/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.27/2.00  
% 5.27/2.00  Inference rules
% 5.27/2.00  ----------------------
% 5.27/2.00  #Ref     : 0
% 5.27/2.00  #Sup     : 726
% 5.27/2.00  #Fact    : 4
% 5.27/2.00  #Define  : 0
% 5.27/2.00  #Split   : 7
% 5.27/2.00  #Chain   : 0
% 5.27/2.00  #Close   : 0
% 5.27/2.00  
% 5.27/2.00  Ordering : KBO
% 5.27/2.00  
% 5.27/2.00  Simplification rules
% 5.27/2.00  ----------------------
% 5.27/2.00  #Subsume      : 224
% 5.27/2.00  #Demod        : 158
% 5.27/2.00  #Tautology    : 75
% 5.27/2.00  #SimpNegUnit  : 15
% 5.27/2.00  #BackRed      : 39
% 5.27/2.00  
% 5.27/2.00  #Partial instantiations: 0
% 5.27/2.00  #Strategies tried      : 1
% 5.27/2.00  
% 5.27/2.00  Timing (in seconds)
% 5.27/2.00  ----------------------
% 5.27/2.01  Preprocessing        : 0.30
% 5.27/2.01  Parsing              : 0.17
% 5.27/2.01  CNF conversion       : 0.02
% 5.27/2.01  Main loop            : 0.93
% 5.27/2.01  Inferencing          : 0.33
% 5.27/2.01  Reduction            : 0.23
% 5.27/2.01  Demodulation         : 0.15
% 5.27/2.01  BG Simplification    : 0.03
% 5.27/2.01  Subsumption          : 0.25
% 5.27/2.01  Abstraction          : 0.03
% 5.27/2.01  MUC search           : 0.00
% 5.27/2.01  Cooper               : 0.00
% 5.27/2.01  Total                : 1.26
% 5.27/2.01  Index Insertion      : 0.00
% 5.27/2.01  Index Deletion       : 0.00
% 5.27/2.01  Index Matching       : 0.00
% 5.27/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
