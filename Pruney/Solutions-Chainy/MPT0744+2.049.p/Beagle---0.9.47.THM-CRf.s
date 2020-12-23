%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:21 EST 2020

% Result     : Theorem 15.93s
% Output     : CNFRefutation 15.93s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 109 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 233 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_80,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_85,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_56,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32565,plain,(
    ! [A_9314,B_9315] :
      ( r1_ordinal1(A_9314,B_9315)
      | ~ r1_tarski(A_9314,B_9315)
      | ~ v3_ordinal1(B_9315)
      | ~ v3_ordinal1(A_9314) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32570,plain,(
    ! [B_9316] :
      ( r1_ordinal1(B_9316,B_9316)
      | ~ v3_ordinal1(B_9316) ) ),
    inference(resolution,[status(thm)],[c_24,c_32565])).

tff(c_58,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32313,plain,(
    ! [B_9293,A_9294] :
      ( r1_ordinal1(B_9293,A_9294)
      | r1_ordinal1(A_9294,B_9293)
      | ~ v3_ordinal1(B_9293)
      | ~ v3_ordinal1(A_9294) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    ! [B_20] : r2_hidden(B_20,k1_ordinal1(B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_66,plain,
    ( r2_hidden('#skF_5',k1_ordinal1('#skF_6'))
    | r1_ordinal1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_96,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_456,plain,(
    ! [B_95,A_96] :
      ( r2_hidden(B_95,A_96)
      | r1_ordinal1(A_96,B_95)
      | ~ v3_ordinal1(B_95)
      | ~ v3_ordinal1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_100,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden(A_37,B_38)
      | r2_hidden(A_37,k1_ordinal1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_60,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_99,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_60])).

tff(c_107,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_99])).

tff(c_535,plain,
    ( r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_456,c_107])).

tff(c_568,plain,(
    r1_ordinal1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_535])).

tff(c_44,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ r1_ordinal1(A_17,B_18)
      | ~ v3_ordinal1(B_18)
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_714,plain,(
    ! [A_111,B_112] :
      ( r1_tarski(A_111,B_112)
      | ~ r1_ordinal1(A_111,B_112)
      | ~ v3_ordinal1(B_112)
      | ~ v3_ordinal1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5265,plain,(
    ! [B_2631,A_2632] :
      ( B_2631 = A_2632
      | ~ r1_tarski(B_2631,A_2632)
      | ~ r1_ordinal1(A_2632,B_2631)
      | ~ v3_ordinal1(B_2631)
      | ~ v3_ordinal1(A_2632) ) ),
    inference(resolution,[status(thm)],[c_714,c_20])).

tff(c_31960,plain,(
    ! [B_9235,A_9236] :
      ( B_9235 = A_9236
      | ~ r1_ordinal1(B_9235,A_9236)
      | ~ r1_ordinal1(A_9236,B_9235)
      | ~ v3_ordinal1(B_9235)
      | ~ v3_ordinal1(A_9236) ) ),
    inference(resolution,[status(thm)],[c_44,c_5265])).

tff(c_31982,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_568,c_31960])).

tff(c_32003,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_96,c_31982])).

tff(c_32018,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32003,c_99])).

tff(c_32023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_32018])).

tff(c_32025,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_32316,plain,
    ( r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32313,c_32025])).

tff(c_32322,plain,(
    r1_ordinal1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_32316])).

tff(c_32513,plain,(
    ! [A_9312,B_9313] :
      ( r1_tarski(A_9312,B_9313)
      | ~ r1_ordinal1(A_9312,B_9313)
      | ~ v3_ordinal1(B_9313)
      | ~ v3_ordinal1(A_9312) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32024,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_32244,plain,(
    ! [B_9281,A_9282] :
      ( B_9281 = A_9282
      | r2_hidden(A_9282,B_9281)
      | ~ r2_hidden(A_9282,k1_ordinal1(B_9281)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32255,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_32024,c_32244])).

tff(c_32258,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_32255])).

tff(c_54,plain,(
    ! [B_25,A_24] :
      ( ~ r1_tarski(B_25,A_24)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32262,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_32258,c_54])).

tff(c_32527,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32513,c_32262])).

tff(c_32551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_32322,c_32527])).

tff(c_32552,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32255])).

tff(c_32556,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32552,c_32025])).

tff(c_32573,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32570,c_32556])).

tff(c_32577,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_32573])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n011.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 20:48:27 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.93/7.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.93/7.09  
% 15.93/7.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.93/7.09  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 15.93/7.09  
% 15.93/7.09  %Foreground sorts:
% 15.93/7.09  
% 15.93/7.09  
% 15.93/7.09  %Background operators:
% 15.93/7.09  
% 15.93/7.09  
% 15.93/7.09  %Foreground operators:
% 15.93/7.09  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 15.93/7.09  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 15.93/7.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.93/7.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.93/7.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.93/7.09  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 15.93/7.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.93/7.09  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 15.93/7.09  tff('#skF_5', type, '#skF_5': $i).
% 15.93/7.09  tff('#skF_6', type, '#skF_6': $i).
% 15.93/7.09  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.93/7.09  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 15.93/7.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.93/7.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.93/7.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.93/7.09  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 15.93/7.09  
% 15.93/7.10  tff(f_95, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 15.93/7.10  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.93/7.10  tff(f_65, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 15.93/7.10  tff(f_55, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 15.93/7.10  tff(f_71, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 15.93/7.10  tff(f_80, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 15.93/7.10  tff(f_85, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 15.93/7.10  tff(c_56, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.93/7.10  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.93/7.10  tff(c_32565, plain, (![A_9314, B_9315]: (r1_ordinal1(A_9314, B_9315) | ~r1_tarski(A_9314, B_9315) | ~v3_ordinal1(B_9315) | ~v3_ordinal1(A_9314))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.93/7.10  tff(c_32570, plain, (![B_9316]: (r1_ordinal1(B_9316, B_9316) | ~v3_ordinal1(B_9316))), inference(resolution, [status(thm)], [c_24, c_32565])).
% 15.93/7.10  tff(c_58, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.93/7.10  tff(c_32313, plain, (![B_9293, A_9294]: (r1_ordinal1(B_9293, A_9294) | r1_ordinal1(A_9294, B_9293) | ~v3_ordinal1(B_9293) | ~v3_ordinal1(A_9294))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.93/7.10  tff(c_48, plain, (![B_20]: (r2_hidden(B_20, k1_ordinal1(B_20)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.93/7.10  tff(c_66, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6')) | r1_ordinal1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.93/7.10  tff(c_96, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_66])).
% 15.93/7.10  tff(c_456, plain, (![B_95, A_96]: (r2_hidden(B_95, A_96) | r1_ordinal1(A_96, B_95) | ~v3_ordinal1(B_95) | ~v3_ordinal1(A_96))), inference(cnfTransformation, [status(thm)], [f_80])).
% 15.93/7.10  tff(c_100, plain, (![A_37, B_38]: (~r2_hidden(A_37, B_38) | r2_hidden(A_37, k1_ordinal1(B_38)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.93/7.10  tff(c_60, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.93/7.10  tff(c_99, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_60])).
% 15.93/7.10  tff(c_107, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_100, c_99])).
% 15.93/7.10  tff(c_535, plain, (r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_456, c_107])).
% 15.93/7.10  tff(c_568, plain, (r1_ordinal1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_535])).
% 15.93/7.10  tff(c_44, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~r1_ordinal1(A_17, B_18) | ~v3_ordinal1(B_18) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.93/7.10  tff(c_714, plain, (![A_111, B_112]: (r1_tarski(A_111, B_112) | ~r1_ordinal1(A_111, B_112) | ~v3_ordinal1(B_112) | ~v3_ordinal1(A_111))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.93/7.10  tff(c_20, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.93/7.10  tff(c_5265, plain, (![B_2631, A_2632]: (B_2631=A_2632 | ~r1_tarski(B_2631, A_2632) | ~r1_ordinal1(A_2632, B_2631) | ~v3_ordinal1(B_2631) | ~v3_ordinal1(A_2632))), inference(resolution, [status(thm)], [c_714, c_20])).
% 15.93/7.10  tff(c_31960, plain, (![B_9235, A_9236]: (B_9235=A_9236 | ~r1_ordinal1(B_9235, A_9236) | ~r1_ordinal1(A_9236, B_9235) | ~v3_ordinal1(B_9235) | ~v3_ordinal1(A_9236))), inference(resolution, [status(thm)], [c_44, c_5265])).
% 15.93/7.10  tff(c_31982, plain, ('#skF_5'='#skF_6' | ~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_568, c_31960])).
% 15.93/7.10  tff(c_32003, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_96, c_31982])).
% 15.93/7.10  tff(c_32018, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_32003, c_99])).
% 15.93/7.10  tff(c_32023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_32018])).
% 15.93/7.10  tff(c_32025, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_66])).
% 15.93/7.10  tff(c_32316, plain, (r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_32313, c_32025])).
% 15.93/7.10  tff(c_32322, plain, (r1_ordinal1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_32316])).
% 15.93/7.10  tff(c_32513, plain, (![A_9312, B_9313]: (r1_tarski(A_9312, B_9313) | ~r1_ordinal1(A_9312, B_9313) | ~v3_ordinal1(B_9313) | ~v3_ordinal1(A_9312))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.93/7.10  tff(c_32024, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(splitRight, [status(thm)], [c_66])).
% 15.93/7.10  tff(c_32244, plain, (![B_9281, A_9282]: (B_9281=A_9282 | r2_hidden(A_9282, B_9281) | ~r2_hidden(A_9282, k1_ordinal1(B_9281)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.93/7.10  tff(c_32255, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_32024, c_32244])).
% 15.93/7.10  tff(c_32258, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_32255])).
% 15.93/7.10  tff(c_54, plain, (![B_25, A_24]: (~r1_tarski(B_25, A_24) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_85])).
% 15.93/7.10  tff(c_32262, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_32258, c_54])).
% 15.93/7.10  tff(c_32527, plain, (~r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_32513, c_32262])).
% 15.93/7.10  tff(c_32551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_32322, c_32527])).
% 15.93/7.10  tff(c_32552, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_32255])).
% 15.93/7.10  tff(c_32556, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32552, c_32025])).
% 15.93/7.10  tff(c_32573, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_32570, c_32556])).
% 15.93/7.10  tff(c_32577, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_32573])).
% 15.93/7.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.93/7.10  
% 15.93/7.10  Inference rules
% 15.93/7.10  ----------------------
% 15.93/7.10  #Ref     : 0
% 15.93/7.10  #Sup     : 6467
% 15.93/7.10  #Fact    : 14
% 15.93/7.10  #Define  : 0
% 15.93/7.10  #Split   : 6
% 15.93/7.10  #Chain   : 0
% 15.93/7.10  #Close   : 0
% 15.93/7.10  
% 15.93/7.10  Ordering : KBO
% 15.93/7.10  
% 15.93/7.10  Simplification rules
% 15.93/7.10  ----------------------
% 15.93/7.10  #Subsume      : 2628
% 15.93/7.10  #Demod        : 225
% 15.93/7.10  #Tautology    : 197
% 15.93/7.10  #SimpNegUnit  : 100
% 15.93/7.10  #BackRed      : 15
% 15.93/7.10  
% 15.93/7.10  #Partial instantiations: 4923
% 15.93/7.10  #Strategies tried      : 1
% 15.93/7.10  
% 15.93/7.10  Timing (in seconds)
% 15.93/7.10  ----------------------
% 15.93/7.10  Preprocessing        : 0.31
% 15.93/7.10  Parsing              : 0.16
% 15.93/7.10  CNF conversion       : 0.03
% 15.93/7.10  Main loop            : 6.06
% 15.93/7.10  Inferencing          : 1.17
% 15.93/7.11  Reduction            : 1.78
% 15.93/7.11  Demodulation         : 0.63
% 15.93/7.11  BG Simplification    : 0.12
% 15.93/7.11  Subsumption          : 2.63
% 15.93/7.11  Abstraction          : 0.21
% 15.93/7.11  MUC search           : 0.00
% 15.93/7.11  Cooper               : 0.00
% 15.93/7.11  Total                : 6.40
% 15.93/7.11  Index Insertion      : 0.00
% 15.93/7.11  Index Deletion       : 0.00
% 15.93/7.11  Index Matching       : 0.00
% 15.93/7.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
