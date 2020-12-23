%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:45 EST 2020

% Result     : Theorem 8.12s
% Output     : CNFRefutation 8.12s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 106 expanded)
%              Number of leaves         :   28 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :   93 ( 199 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_60,axiom,(
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

tff(f_91,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_116,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_95,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_315,plain,(
    ! [A_98,B_99] :
      ( r2_hidden('#skF_3'(A_98,B_99),B_99)
      | r1_xboole_0(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    ! [B_40,A_39] :
      ( ~ v1_xboole_0(B_40)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_458,plain,(
    ! [B_108,A_109] :
      ( ~ v1_xboole_0(B_108)
      | r1_xboole_0(A_109,B_108) ) ),
    inference(resolution,[status(thm)],[c_315,c_46])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [B_66] :
      ( ~ r1_xboole_0(B_66,'#skF_5')
      | ~ r2_hidden(B_66,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_107,plain,
    ( ~ r1_xboole_0('#skF_1'('#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_102])).

tff(c_108,plain,(
    ~ r1_xboole_0('#skF_1'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_474,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_458,c_108])).

tff(c_26,plain,(
    ! [B_18] : r1_tarski(B_18,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),B_13)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),A_12)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2036,plain,(
    ! [D_206,A_207,B_208] :
      ( ~ r2_hidden(D_206,'#skF_4'(A_207,B_208))
      | ~ r2_hidden(D_206,B_208)
      | ~ r2_hidden(A_207,B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_13978,plain,(
    ! [A_538,B_539,B_540] :
      ( ~ r2_hidden('#skF_3'('#skF_4'(A_538,B_539),B_540),B_539)
      | ~ r2_hidden(A_538,B_539)
      | r1_xboole_0('#skF_4'(A_538,B_539),B_540) ) ),
    inference(resolution,[status(thm)],[c_20,c_2036])).

tff(c_13994,plain,(
    ! [A_541,B_542] :
      ( ~ r2_hidden(A_541,B_542)
      | r1_xboole_0('#skF_4'(A_541,B_542),B_542) ) ),
    inference(resolution,[status(thm)],[c_18,c_13978])).

tff(c_62,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_4'(A_47,B_48),B_48)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1549,plain,(
    ! [C_189,B_190,A_191] :
      ( r2_hidden(C_189,B_190)
      | ~ r2_hidden(C_189,A_191)
      | ~ r1_tarski(A_191,B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6175,plain,(
    ! [A_315,B_316,B_317] :
      ( r2_hidden('#skF_4'(A_315,B_316),B_317)
      | ~ r1_tarski(B_316,B_317)
      | ~ r2_hidden(A_315,B_316) ) ),
    inference(resolution,[status(thm)],[c_62,c_1549])).

tff(c_64,plain,(
    ! [B_55] :
      ( ~ r1_xboole_0(B_55,'#skF_5')
      | ~ r2_hidden(B_55,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6225,plain,(
    ! [A_315,B_316] :
      ( ~ r1_xboole_0('#skF_4'(A_315,B_316),'#skF_5')
      | ~ r1_tarski(B_316,'#skF_5')
      | ~ r2_hidden(A_315,B_316) ) ),
    inference(resolution,[status(thm)],[c_6175,c_64])).

tff(c_14002,plain,(
    ! [A_541] :
      ( ~ r1_tarski('#skF_5','#skF_5')
      | ~ r2_hidden(A_541,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_13994,c_6225])).

tff(c_14023,plain,(
    ! [A_543] : ~ r2_hidden(A_543,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14002])).

tff(c_14063,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_14023])).

tff(c_14076,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_474,c_14063])).

tff(c_14077,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_14264,plain,(
    ! [A_572,B_573] :
      ( r2_hidden('#skF_3'(A_572,B_573),A_572)
      | r1_xboole_0(A_572,B_573) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14274,plain,(
    ! [A_574,B_575] :
      ( ~ v1_xboole_0(A_574)
      | r1_xboole_0(A_574,B_575) ) ),
    inference(resolution,[status(thm)],[c_14264,c_46])).

tff(c_48,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = A_41
      | ~ r1_xboole_0(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_14358,plain,(
    ! [A_582,B_583] :
      ( k4_xboole_0(A_582,B_583) = A_582
      | ~ v1_xboole_0(A_582) ) ),
    inference(resolution,[status(thm)],[c_14274,c_48])).

tff(c_14361,plain,(
    ! [B_583] : k4_xboole_0('#skF_5',B_583) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_14077,c_14358])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14287,plain,(
    ! [A_576,B_577] :
      ( k3_xboole_0(A_576,B_577) = k1_xboole_0
      | ~ v1_xboole_0(A_576) ) ),
    inference(resolution,[status(thm)],[c_14274,c_12])).

tff(c_14290,plain,(
    ! [B_577] : k3_xboole_0('#skF_5',B_577) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14077,c_14287])).

tff(c_14782,plain,(
    ! [A_617,B_618] : k4_xboole_0(A_617,k4_xboole_0(A_617,B_618)) = k3_xboole_0(A_617,B_618) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14820,plain,(
    ! [B_583] : k4_xboole_0('#skF_5','#skF_5') = k3_xboole_0('#skF_5',B_583) ),
    inference(superposition,[status(thm),theory(equality)],[c_14361,c_14782])).

tff(c_14836,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14361,c_14290,c_14820])).

tff(c_14838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_14836])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:46:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.12/2.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.12/2.93  
% 8.12/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.12/2.94  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 8.12/2.94  
% 8.12/2.94  %Foreground sorts:
% 8.12/2.94  
% 8.12/2.94  
% 8.12/2.94  %Background operators:
% 8.12/2.94  
% 8.12/2.94  
% 8.12/2.94  %Foreground operators:
% 8.12/2.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.12/2.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.12/2.94  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.12/2.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.12/2.94  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.12/2.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.12/2.94  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.12/2.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.12/2.94  tff('#skF_5', type, '#skF_5': $i).
% 8.12/2.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.12/2.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.12/2.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.12/2.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.12/2.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.12/2.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.12/2.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.12/2.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.12/2.94  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.12/2.94  
% 8.12/2.95  tff(f_127, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 8.12/2.95  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.12/2.95  tff(f_91, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 8.12/2.95  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.12/2.95  tff(f_66, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.12/2.95  tff(f_116, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 8.12/2.95  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.12/2.95  tff(f_95, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 8.12/2.95  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.12/2.95  tff(f_76, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.12/2.95  tff(c_66, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.12/2.95  tff(c_315, plain, (![A_98, B_99]: (r2_hidden('#skF_3'(A_98, B_99), B_99) | r1_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.12/2.95  tff(c_46, plain, (![B_40, A_39]: (~v1_xboole_0(B_40) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.12/2.95  tff(c_458, plain, (![B_108, A_109]: (~v1_xboole_0(B_108) | r1_xboole_0(A_109, B_108))), inference(resolution, [status(thm)], [c_315, c_46])).
% 8.12/2.95  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.12/2.95  tff(c_102, plain, (![B_66]: (~r1_xboole_0(B_66, '#skF_5') | ~r2_hidden(B_66, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.12/2.95  tff(c_107, plain, (~r1_xboole_0('#skF_1'('#skF_5'), '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_102])).
% 8.12/2.95  tff(c_108, plain, (~r1_xboole_0('#skF_1'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_107])).
% 8.12/2.95  tff(c_474, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_458, c_108])).
% 8.12/2.95  tff(c_26, plain, (![B_18]: (r1_tarski(B_18, B_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.12/2.95  tff(c_18, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), B_13) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.12/2.95  tff(c_20, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), A_12) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.12/2.95  tff(c_2036, plain, (![D_206, A_207, B_208]: (~r2_hidden(D_206, '#skF_4'(A_207, B_208)) | ~r2_hidden(D_206, B_208) | ~r2_hidden(A_207, B_208))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.12/2.95  tff(c_13978, plain, (![A_538, B_539, B_540]: (~r2_hidden('#skF_3'('#skF_4'(A_538, B_539), B_540), B_539) | ~r2_hidden(A_538, B_539) | r1_xboole_0('#skF_4'(A_538, B_539), B_540))), inference(resolution, [status(thm)], [c_20, c_2036])).
% 8.12/2.95  tff(c_13994, plain, (![A_541, B_542]: (~r2_hidden(A_541, B_542) | r1_xboole_0('#skF_4'(A_541, B_542), B_542))), inference(resolution, [status(thm)], [c_18, c_13978])).
% 8.12/2.95  tff(c_62, plain, (![A_47, B_48]: (r2_hidden('#skF_4'(A_47, B_48), B_48) | ~r2_hidden(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.12/2.95  tff(c_1549, plain, (![C_189, B_190, A_191]: (r2_hidden(C_189, B_190) | ~r2_hidden(C_189, A_191) | ~r1_tarski(A_191, B_190))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.12/2.95  tff(c_6175, plain, (![A_315, B_316, B_317]: (r2_hidden('#skF_4'(A_315, B_316), B_317) | ~r1_tarski(B_316, B_317) | ~r2_hidden(A_315, B_316))), inference(resolution, [status(thm)], [c_62, c_1549])).
% 8.12/2.95  tff(c_64, plain, (![B_55]: (~r1_xboole_0(B_55, '#skF_5') | ~r2_hidden(B_55, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.12/2.95  tff(c_6225, plain, (![A_315, B_316]: (~r1_xboole_0('#skF_4'(A_315, B_316), '#skF_5') | ~r1_tarski(B_316, '#skF_5') | ~r2_hidden(A_315, B_316))), inference(resolution, [status(thm)], [c_6175, c_64])).
% 8.12/2.95  tff(c_14002, plain, (![A_541]: (~r1_tarski('#skF_5', '#skF_5') | ~r2_hidden(A_541, '#skF_5'))), inference(resolution, [status(thm)], [c_13994, c_6225])).
% 8.12/2.95  tff(c_14023, plain, (![A_543]: (~r2_hidden(A_543, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_14002])).
% 8.12/2.95  tff(c_14063, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_14023])).
% 8.12/2.95  tff(c_14076, plain, $false, inference(negUnitSimplification, [status(thm)], [c_474, c_14063])).
% 8.12/2.95  tff(c_14077, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_107])).
% 8.12/2.95  tff(c_14264, plain, (![A_572, B_573]: (r2_hidden('#skF_3'(A_572, B_573), A_572) | r1_xboole_0(A_572, B_573))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.12/2.95  tff(c_14274, plain, (![A_574, B_575]: (~v1_xboole_0(A_574) | r1_xboole_0(A_574, B_575))), inference(resolution, [status(thm)], [c_14264, c_46])).
% 8.12/2.95  tff(c_48, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=A_41 | ~r1_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.12/2.95  tff(c_14358, plain, (![A_582, B_583]: (k4_xboole_0(A_582, B_583)=A_582 | ~v1_xboole_0(A_582))), inference(resolution, [status(thm)], [c_14274, c_48])).
% 8.12/2.95  tff(c_14361, plain, (![B_583]: (k4_xboole_0('#skF_5', B_583)='#skF_5')), inference(resolution, [status(thm)], [c_14077, c_14358])).
% 8.12/2.95  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.12/2.95  tff(c_14287, plain, (![A_576, B_577]: (k3_xboole_0(A_576, B_577)=k1_xboole_0 | ~v1_xboole_0(A_576))), inference(resolution, [status(thm)], [c_14274, c_12])).
% 8.12/2.95  tff(c_14290, plain, (![B_577]: (k3_xboole_0('#skF_5', B_577)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14077, c_14287])).
% 8.12/2.95  tff(c_14782, plain, (![A_617, B_618]: (k4_xboole_0(A_617, k4_xboole_0(A_617, B_618))=k3_xboole_0(A_617, B_618))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.12/2.95  tff(c_14820, plain, (![B_583]: (k4_xboole_0('#skF_5', '#skF_5')=k3_xboole_0('#skF_5', B_583))), inference(superposition, [status(thm), theory('equality')], [c_14361, c_14782])).
% 8.12/2.95  tff(c_14836, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_14361, c_14290, c_14820])).
% 8.12/2.95  tff(c_14838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_14836])).
% 8.12/2.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.12/2.95  
% 8.12/2.95  Inference rules
% 8.12/2.95  ----------------------
% 8.12/2.95  #Ref     : 1
% 8.12/2.95  #Sup     : 3835
% 8.12/2.95  #Fact    : 0
% 8.12/2.95  #Define  : 0
% 8.12/2.95  #Split   : 1
% 8.12/2.95  #Chain   : 0
% 8.12/2.95  #Close   : 0
% 8.12/2.95  
% 8.12/2.95  Ordering : KBO
% 8.12/2.95  
% 8.12/2.95  Simplification rules
% 8.12/2.95  ----------------------
% 8.12/2.95  #Subsume      : 1221
% 8.12/2.95  #Demod        : 1607
% 8.12/2.95  #Tautology    : 1518
% 8.12/2.95  #SimpNegUnit  : 20
% 8.12/2.95  #BackRed      : 0
% 8.12/2.95  
% 8.12/2.95  #Partial instantiations: 0
% 8.12/2.95  #Strategies tried      : 1
% 8.12/2.95  
% 8.12/2.95  Timing (in seconds)
% 8.12/2.95  ----------------------
% 8.12/2.95  Preprocessing        : 0.32
% 8.12/2.95  Parsing              : 0.17
% 8.12/2.95  CNF conversion       : 0.02
% 8.12/2.95  Main loop            : 1.87
% 8.12/2.95  Inferencing          : 0.53
% 8.12/2.95  Reduction            : 0.71
% 8.12/2.95  Demodulation         : 0.53
% 8.12/2.95  BG Simplification    : 0.06
% 8.12/2.95  Subsumption          : 0.44
% 8.12/2.95  Abstraction          : 0.08
% 8.12/2.95  MUC search           : 0.00
% 8.12/2.95  Cooper               : 0.00
% 8.12/2.95  Total                : 2.22
% 8.12/2.95  Index Insertion      : 0.00
% 8.12/2.95  Index Deletion       : 0.00
% 8.12/2.95  Index Matching       : 0.00
% 8.12/2.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
