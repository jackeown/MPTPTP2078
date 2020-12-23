%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:03 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 165 expanded)
%              Number of leaves         :   21 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  108 ( 413 expanded)
%              Number of equality atoms :   19 (  49 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( v1_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ! [C] :
                ( v3_ordinal1(C)
               => ( ( r1_tarski(A,B)
                    & r2_hidden(B,C) )
                 => r2_hidden(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).

tff(f_50,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r2_xboole_0(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l58_xboole_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_71,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_32,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_36,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_53,plain,(
    ! [A_25] :
      ( v1_ordinal1(A_25)
      | ~ v3_ordinal1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_60,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_53])).

tff(c_74,plain,(
    ! [B_32,A_33] :
      ( r1_tarski(B_32,A_33)
      | ~ r2_hidden(B_32,A_33)
      | ~ v1_ordinal1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_80,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_74])).

tff(c_84,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_80])).

tff(c_12,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_113,plain,(
    ! [A_39,C_40,B_41] :
      ( r2_xboole_0(A_39,C_40)
      | ~ r2_xboole_0(B_41,C_40)
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_122,plain,(
    ! [A_44,B_45,A_46] :
      ( r2_xboole_0(A_44,B_45)
      | ~ r1_tarski(A_44,A_46)
      | B_45 = A_46
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(resolution,[status(thm)],[c_2,c_113])).

tff(c_132,plain,(
    ! [B_47] :
      ( r2_xboole_0('#skF_2',B_47)
      | B_47 = '#skF_3'
      | ~ r1_tarski('#skF_3',B_47) ) ),
    inference(resolution,[status(thm)],[c_34,c_122])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_149,plain,(
    ! [B_47] :
      ( r1_tarski('#skF_2',B_47)
      | B_47 = '#skF_3'
      | ~ r1_tarski('#skF_3',B_47) ) ),
    inference(resolution,[status(thm)],[c_132,c_6])).

tff(c_40,plain,(
    v1_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_117,plain,(
    ! [A_42,B_43] :
      ( r2_hidden(A_42,B_43)
      | ~ r2_xboole_0(A_42,B_43)
      | ~ v3_ordinal1(B_43)
      | ~ v1_ordinal1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_201,plain,(
    ! [A_51,B_52] :
      ( r2_hidden(A_51,B_52)
      | ~ v3_ordinal1(B_52)
      | ~ v1_ordinal1(A_51)
      | B_52 = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_2,c_117])).

tff(c_30,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_210,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_2')
    | '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_201,c_30])).

tff(c_215,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_210])).

tff(c_216,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_219,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_149,c_216])).

tff(c_222,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_219])).

tff(c_65,plain,(
    ! [B_30,A_31] :
      ( ~ r1_tarski(B_30,A_31)
      | ~ r2_hidden(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_73,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_65])).

tff(c_229,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_73])).

tff(c_238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_229])).

tff(c_239,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_151,plain,(
    ! [B_48] :
      ( r2_xboole_0('#skF_3',B_48)
      | B_48 = '#skF_4'
      | ~ r1_tarski('#skF_4',B_48) ) ),
    inference(resolution,[status(thm)],[c_84,c_122])).

tff(c_183,plain,(
    ! [B_50] :
      ( r1_tarski('#skF_3',B_50)
      | B_50 = '#skF_4'
      | ~ r1_tarski('#skF_4',B_50) ) ),
    inference(resolution,[status(thm)],[c_151,c_6])).

tff(c_86,plain,(
    ! [B_35,A_36] :
      ( B_35 = A_36
      | ~ r1_tarski(B_35,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_98,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_86])).

tff(c_99,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_196,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_183,c_99])).

tff(c_200,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_259,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_200])).

tff(c_268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_259])).

tff(c_269,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_273,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_99])).

tff(c_279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_273])).

tff(c_280,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_282,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_30])).

tff(c_287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.24  
% 2.20/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.24  %$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.20/1.24  
% 2.20/1.24  %Foreground sorts:
% 2.20/1.24  
% 2.20/1.24  
% 2.20/1.24  %Background operators:
% 2.20/1.24  
% 2.20/1.24  
% 2.20/1.24  %Foreground operators:
% 2.20/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.24  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.20/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.20/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.24  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.20/1.24  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.20/1.24  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.20/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.24  
% 2.20/1.26  tff(f_86, negated_conjecture, ~(![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (![C]: (v3_ordinal1(C) => ((r1_tarski(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_ordinal1)).
% 2.20/1.26  tff(f_50, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.20/1.26  tff(f_57, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.20/1.26  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.20/1.26  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.20/1.26  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l58_xboole_1)).
% 2.20/1.26  tff(f_66, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 2.20/1.26  tff(f_71, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.20/1.26  tff(c_32, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.20/1.26  tff(c_36, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.20/1.26  tff(c_53, plain, (![A_25]: (v1_ordinal1(A_25) | ~v3_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.20/1.26  tff(c_60, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_53])).
% 2.20/1.26  tff(c_74, plain, (![B_32, A_33]: (r1_tarski(B_32, A_33) | ~r2_hidden(B_32, A_33) | ~v1_ordinal1(A_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.26  tff(c_80, plain, (r1_tarski('#skF_3', '#skF_4') | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_74])).
% 2.20/1.26  tff(c_84, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_80])).
% 2.20/1.26  tff(c_12, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.20/1.26  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.20/1.26  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.20/1.26  tff(c_113, plain, (![A_39, C_40, B_41]: (r2_xboole_0(A_39, C_40) | ~r2_xboole_0(B_41, C_40) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.20/1.26  tff(c_122, plain, (![A_44, B_45, A_46]: (r2_xboole_0(A_44, B_45) | ~r1_tarski(A_44, A_46) | B_45=A_46 | ~r1_tarski(A_46, B_45))), inference(resolution, [status(thm)], [c_2, c_113])).
% 2.20/1.26  tff(c_132, plain, (![B_47]: (r2_xboole_0('#skF_2', B_47) | B_47='#skF_3' | ~r1_tarski('#skF_3', B_47))), inference(resolution, [status(thm)], [c_34, c_122])).
% 2.20/1.26  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.20/1.26  tff(c_149, plain, (![B_47]: (r1_tarski('#skF_2', B_47) | B_47='#skF_3' | ~r1_tarski('#skF_3', B_47))), inference(resolution, [status(thm)], [c_132, c_6])).
% 2.20/1.26  tff(c_40, plain, (v1_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.20/1.26  tff(c_117, plain, (![A_42, B_43]: (r2_hidden(A_42, B_43) | ~r2_xboole_0(A_42, B_43) | ~v3_ordinal1(B_43) | ~v1_ordinal1(A_42))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.20/1.26  tff(c_201, plain, (![A_51, B_52]: (r2_hidden(A_51, B_52) | ~v3_ordinal1(B_52) | ~v1_ordinal1(A_51) | B_52=A_51 | ~r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_2, c_117])).
% 2.20/1.26  tff(c_30, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.20/1.26  tff(c_210, plain, (~v3_ordinal1('#skF_4') | ~v1_ordinal1('#skF_2') | '#skF_2'='#skF_4' | ~r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_201, c_30])).
% 2.20/1.26  tff(c_215, plain, ('#skF_2'='#skF_4' | ~r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_210])).
% 2.20/1.26  tff(c_216, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_215])).
% 2.20/1.26  tff(c_219, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_149, c_216])).
% 2.20/1.26  tff(c_222, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_219])).
% 2.20/1.26  tff(c_65, plain, (![B_30, A_31]: (~r1_tarski(B_30, A_31) | ~r2_hidden(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.20/1.26  tff(c_73, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_65])).
% 2.20/1.26  tff(c_229, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_73])).
% 2.20/1.26  tff(c_238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_229])).
% 2.20/1.26  tff(c_239, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_215])).
% 2.20/1.26  tff(c_151, plain, (![B_48]: (r2_xboole_0('#skF_3', B_48) | B_48='#skF_4' | ~r1_tarski('#skF_4', B_48))), inference(resolution, [status(thm)], [c_84, c_122])).
% 2.20/1.26  tff(c_183, plain, (![B_50]: (r1_tarski('#skF_3', B_50) | B_50='#skF_4' | ~r1_tarski('#skF_4', B_50))), inference(resolution, [status(thm)], [c_151, c_6])).
% 2.20/1.26  tff(c_86, plain, (![B_35, A_36]: (B_35=A_36 | ~r1_tarski(B_35, A_36) | ~r1_tarski(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.20/1.26  tff(c_98, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_86])).
% 2.20/1.26  tff(c_99, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_98])).
% 2.20/1.26  tff(c_196, plain, ('#skF_2'='#skF_4' | ~r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_183, c_99])).
% 2.20/1.26  tff(c_200, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_196])).
% 2.20/1.26  tff(c_259, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_200])).
% 2.20/1.26  tff(c_268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_259])).
% 2.20/1.26  tff(c_269, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_196])).
% 2.20/1.26  tff(c_273, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_99])).
% 2.20/1.26  tff(c_279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_273])).
% 2.20/1.26  tff(c_280, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_98])).
% 2.20/1.26  tff(c_282, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_280, c_30])).
% 2.20/1.26  tff(c_287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_282])).
% 2.20/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.26  
% 2.20/1.26  Inference rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Ref     : 0
% 2.20/1.26  #Sup     : 41
% 2.20/1.26  #Fact    : 0
% 2.20/1.26  #Define  : 0
% 2.20/1.26  #Split   : 3
% 2.20/1.26  #Chain   : 0
% 2.20/1.26  #Close   : 0
% 2.20/1.26  
% 2.20/1.26  Ordering : KBO
% 2.20/1.26  
% 2.20/1.26  Simplification rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Subsume      : 7
% 2.20/1.26  #Demod        : 47
% 2.20/1.26  #Tautology    : 10
% 2.20/1.26  #SimpNegUnit  : 0
% 2.20/1.26  #BackRed      : 28
% 2.20/1.26  
% 2.20/1.26  #Partial instantiations: 0
% 2.20/1.26  #Strategies tried      : 1
% 2.20/1.26  
% 2.20/1.26  Timing (in seconds)
% 2.20/1.26  ----------------------
% 2.20/1.26  Preprocessing        : 0.28
% 2.20/1.26  Parsing              : 0.16
% 2.20/1.26  CNF conversion       : 0.02
% 2.20/1.26  Main loop            : 0.22
% 2.20/1.26  Inferencing          : 0.08
% 2.20/1.26  Reduction            : 0.06
% 2.20/1.26  Demodulation         : 0.04
% 2.20/1.26  BG Simplification    : 0.02
% 2.20/1.26  Subsumption          : 0.05
% 2.20/1.26  Abstraction          : 0.01
% 2.20/1.26  MUC search           : 0.00
% 2.20/1.26  Cooper               : 0.00
% 2.20/1.26  Total                : 0.54
% 2.20/1.26  Index Insertion      : 0.00
% 2.20/1.26  Index Deletion       : 0.00
% 2.20/1.26  Index Matching       : 0.00
% 2.20/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
