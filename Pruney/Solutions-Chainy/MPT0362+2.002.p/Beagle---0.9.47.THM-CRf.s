%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:32 EST 2020

% Result     : Theorem 4.34s
% Output     : CNFRefutation 4.34s
% Verified   : 
% Statistics : Number of formulae       :   69 (  95 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  104 ( 169 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_72,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_194,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),A_60)
      | r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1254,plain,(
    ! [A_162,B_163,B_164] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_162,B_163),B_164),A_162)
      | r1_tarski(k3_xboole_0(A_162,B_163),B_164) ) ),
    inference(resolution,[status(thm)],[c_194,c_14])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1286,plain,(
    ! [A_162,B_163] : r1_tarski(k3_xboole_0(A_162,B_163),A_162) ),
    inference(resolution,[status(thm)],[c_1254,c_6])).

tff(c_50,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    ! [C_21,A_17] :
      ( r1_tarski(C_21,A_17)
      | ~ r2_hidden(C_21,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_218,plain,(
    ! [A_17,B_61] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_17),B_61),A_17)
      | r1_tarski(k1_zfmisc_1(A_17),B_61) ) ),
    inference(resolution,[status(thm)],[c_194,c_30])).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_123,plain,(
    ! [B_46,A_47] :
      ( r2_hidden(B_46,A_47)
      | ~ m1_subset_1(B_46,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_131,plain,(
    ! [B_46,A_17] :
      ( r1_tarski(B_46,A_17)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_123,c_30])).

tff(c_136,plain,(
    ! [B_48,A_49] :
      ( r1_tarski(B_48,A_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_131])).

tff(c_149,plain,(
    r1_tarski('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_136])).

tff(c_230,plain,(
    ! [A_66,C_67,B_68] :
      ( r1_tarski(A_66,C_67)
      | ~ r1_tarski(B_68,C_67)
      | ~ r1_tarski(A_66,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_238,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,'#skF_6')
      | ~ r1_tarski(A_66,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_149,c_230])).

tff(c_32,plain,(
    ! [C_21,A_17] :
      ( r2_hidden(C_21,k1_zfmisc_1(A_17))
      | ~ r1_tarski(C_21,A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_117,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden('#skF_1'(A_44,B_45),B_45)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_364,plain,(
    ! [A_89,A_90] :
      ( r1_tarski(A_89,k1_zfmisc_1(A_90))
      | ~ r1_tarski('#skF_1'(A_89,k1_zfmisc_1(A_90)),A_90) ) ),
    inference(resolution,[status(thm)],[c_32,c_117])).

tff(c_487,plain,(
    ! [A_103] :
      ( r1_tarski(A_103,k1_zfmisc_1('#skF_6'))
      | ~ r1_tarski('#skF_1'(A_103,k1_zfmisc_1('#skF_6')),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_238,c_364])).

tff(c_492,plain,(
    r1_tarski(k1_zfmisc_1('#skF_8'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_218,c_487])).

tff(c_219,plain,(
    ! [C_62,B_63,A_64] :
      ( r2_hidden(C_62,B_63)
      | ~ r2_hidden(C_62,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_228,plain,(
    ! [C_21,B_63,A_17] :
      ( r2_hidden(C_21,B_63)
      | ~ r1_tarski(k1_zfmisc_1(A_17),B_63)
      | ~ r1_tarski(C_21,A_17) ) ),
    inference(resolution,[status(thm)],[c_32,c_219])).

tff(c_531,plain,(
    ! [C_105] :
      ( r2_hidden(C_105,k1_zfmisc_1('#skF_6'))
      | ~ r1_tarski(C_105,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_492,c_228])).

tff(c_42,plain,(
    ! [B_23,A_22] :
      ( m1_subset_1(B_23,A_22)
      | ~ r2_hidden(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_539,plain,(
    ! [C_105] :
      ( m1_subset_1(C_105,k1_zfmisc_1('#skF_6'))
      | v1_xboole_0(k1_zfmisc_1('#skF_6'))
      | ~ r1_tarski(C_105,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_531,c_42])).

tff(c_551,plain,(
    ! [C_105] :
      ( m1_subset_1(C_105,k1_zfmisc_1('#skF_6'))
      | ~ r1_tarski(C_105,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_539])).

tff(c_62,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1288,plain,(
    ! [A_165,B_166] : r1_tarski(k3_xboole_0(A_165,B_166),A_165) ),
    inference(resolution,[status(thm)],[c_1254,c_6])).

tff(c_1317,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1288])).

tff(c_1895,plain,(
    ! [A_198,C_199,B_200] :
      ( r1_tarski(k3_subset_1(A_198,C_199),k3_subset_1(A_198,B_200))
      | ~ r1_tarski(B_200,C_199)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(A_198))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(A_198)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_330,plain,(
    ! [A_84,B_85,C_86] :
      ( k9_subset_1(A_84,B_85,C_86) = k3_xboole_0(B_85,C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_343,plain,(
    ! [B_85] : k9_subset_1('#skF_6',B_85,'#skF_8') = k3_xboole_0(B_85,'#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_330])).

tff(c_58,plain,(
    ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),k3_subset_1('#skF_6',k9_subset_1('#skF_6','#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_353,plain,(
    ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),k3_subset_1('#skF_6',k3_xboole_0('#skF_7','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_58])).

tff(c_354,plain,(
    ~ r1_tarski(k3_subset_1('#skF_6','#skF_7'),k3_subset_1('#skF_6',k3_xboole_0('#skF_8','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_353])).

tff(c_1907,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_8','#skF_7'),'#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1(k3_xboole_0('#skF_8','#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1895,c_354])).

tff(c_1920,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_8','#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1317,c_1907])).

tff(c_1929,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_8','#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_551,c_1920])).

tff(c_1943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1286,c_1929])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:56:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.34/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.34/1.87  
% 4.34/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.34/1.87  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 4.34/1.87  
% 4.34/1.87  %Foreground sorts:
% 4.34/1.87  
% 4.34/1.87  
% 4.34/1.87  %Background operators:
% 4.34/1.87  
% 4.34/1.87  
% 4.34/1.87  %Foreground operators:
% 4.34/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.34/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.34/1.87  tff('#skF_7', type, '#skF_7': $i).
% 4.34/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.34/1.87  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.34/1.87  tff('#skF_6', type, '#skF_6': $i).
% 4.34/1.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.34/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.34/1.87  tff('#skF_8', type, '#skF_8': $i).
% 4.34/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.34/1.87  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.34/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.34/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.34/1.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.34/1.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.34/1.87  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.34/1.87  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.34/1.87  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.34/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.34/1.87  
% 4.34/1.88  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.34/1.88  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.34/1.88  tff(f_72, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.34/1.88  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.34/1.88  tff(f_93, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 4.34/1.88  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.34/1.88  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.34/1.88  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.34/1.88  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 4.34/1.88  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.34/1.88  tff(c_194, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), A_60) | r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.34/1.88  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.34/1.88  tff(c_1254, plain, (![A_162, B_163, B_164]: (r2_hidden('#skF_1'(k3_xboole_0(A_162, B_163), B_164), A_162) | r1_tarski(k3_xboole_0(A_162, B_163), B_164))), inference(resolution, [status(thm)], [c_194, c_14])).
% 4.34/1.88  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.34/1.88  tff(c_1286, plain, (![A_162, B_163]: (r1_tarski(k3_xboole_0(A_162, B_163), A_162))), inference(resolution, [status(thm)], [c_1254, c_6])).
% 4.34/1.88  tff(c_50, plain, (![A_24]: (~v1_xboole_0(k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.34/1.88  tff(c_30, plain, (![C_21, A_17]: (r1_tarski(C_21, A_17) | ~r2_hidden(C_21, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.34/1.88  tff(c_218, plain, (![A_17, B_61]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_17), B_61), A_17) | r1_tarski(k1_zfmisc_1(A_17), B_61))), inference(resolution, [status(thm)], [c_194, c_30])).
% 4.34/1.88  tff(c_60, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.34/1.88  tff(c_123, plain, (![B_46, A_47]: (r2_hidden(B_46, A_47) | ~m1_subset_1(B_46, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.34/1.88  tff(c_131, plain, (![B_46, A_17]: (r1_tarski(B_46, A_17) | ~m1_subset_1(B_46, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_123, c_30])).
% 4.34/1.88  tff(c_136, plain, (![B_48, A_49]: (r1_tarski(B_48, A_49) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)))), inference(negUnitSimplification, [status(thm)], [c_50, c_131])).
% 4.34/1.88  tff(c_149, plain, (r1_tarski('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_136])).
% 4.34/1.88  tff(c_230, plain, (![A_66, C_67, B_68]: (r1_tarski(A_66, C_67) | ~r1_tarski(B_68, C_67) | ~r1_tarski(A_66, B_68))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.34/1.88  tff(c_238, plain, (![A_66]: (r1_tarski(A_66, '#skF_6') | ~r1_tarski(A_66, '#skF_8'))), inference(resolution, [status(thm)], [c_149, c_230])).
% 4.34/1.88  tff(c_32, plain, (![C_21, A_17]: (r2_hidden(C_21, k1_zfmisc_1(A_17)) | ~r1_tarski(C_21, A_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.34/1.88  tff(c_117, plain, (![A_44, B_45]: (~r2_hidden('#skF_1'(A_44, B_45), B_45) | r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.34/1.88  tff(c_364, plain, (![A_89, A_90]: (r1_tarski(A_89, k1_zfmisc_1(A_90)) | ~r1_tarski('#skF_1'(A_89, k1_zfmisc_1(A_90)), A_90))), inference(resolution, [status(thm)], [c_32, c_117])).
% 4.34/1.88  tff(c_487, plain, (![A_103]: (r1_tarski(A_103, k1_zfmisc_1('#skF_6')) | ~r1_tarski('#skF_1'(A_103, k1_zfmisc_1('#skF_6')), '#skF_8'))), inference(resolution, [status(thm)], [c_238, c_364])).
% 4.34/1.88  tff(c_492, plain, (r1_tarski(k1_zfmisc_1('#skF_8'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_218, c_487])).
% 4.34/1.88  tff(c_219, plain, (![C_62, B_63, A_64]: (r2_hidden(C_62, B_63) | ~r2_hidden(C_62, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.34/1.88  tff(c_228, plain, (![C_21, B_63, A_17]: (r2_hidden(C_21, B_63) | ~r1_tarski(k1_zfmisc_1(A_17), B_63) | ~r1_tarski(C_21, A_17))), inference(resolution, [status(thm)], [c_32, c_219])).
% 4.34/1.88  tff(c_531, plain, (![C_105]: (r2_hidden(C_105, k1_zfmisc_1('#skF_6')) | ~r1_tarski(C_105, '#skF_8'))), inference(resolution, [status(thm)], [c_492, c_228])).
% 4.34/1.88  tff(c_42, plain, (![B_23, A_22]: (m1_subset_1(B_23, A_22) | ~r2_hidden(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.34/1.88  tff(c_539, plain, (![C_105]: (m1_subset_1(C_105, k1_zfmisc_1('#skF_6')) | v1_xboole_0(k1_zfmisc_1('#skF_6')) | ~r1_tarski(C_105, '#skF_8'))), inference(resolution, [status(thm)], [c_531, c_42])).
% 4.34/1.88  tff(c_551, plain, (![C_105]: (m1_subset_1(C_105, k1_zfmisc_1('#skF_6')) | ~r1_tarski(C_105, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_50, c_539])).
% 4.34/1.88  tff(c_62, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.34/1.88  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.34/1.88  tff(c_1288, plain, (![A_165, B_166]: (r1_tarski(k3_xboole_0(A_165, B_166), A_165))), inference(resolution, [status(thm)], [c_1254, c_6])).
% 4.34/1.88  tff(c_1317, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1288])).
% 4.34/1.88  tff(c_1895, plain, (![A_198, C_199, B_200]: (r1_tarski(k3_subset_1(A_198, C_199), k3_subset_1(A_198, B_200)) | ~r1_tarski(B_200, C_199) | ~m1_subset_1(C_199, k1_zfmisc_1(A_198)) | ~m1_subset_1(B_200, k1_zfmisc_1(A_198)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.34/1.88  tff(c_330, plain, (![A_84, B_85, C_86]: (k9_subset_1(A_84, B_85, C_86)=k3_xboole_0(B_85, C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.34/1.88  tff(c_343, plain, (![B_85]: (k9_subset_1('#skF_6', B_85, '#skF_8')=k3_xboole_0(B_85, '#skF_8'))), inference(resolution, [status(thm)], [c_60, c_330])).
% 4.34/1.88  tff(c_58, plain, (~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), k3_subset_1('#skF_6', k9_subset_1('#skF_6', '#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.34/1.88  tff(c_353, plain, (~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), k3_subset_1('#skF_6', k3_xboole_0('#skF_7', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_58])).
% 4.34/1.88  tff(c_354, plain, (~r1_tarski(k3_subset_1('#skF_6', '#skF_7'), k3_subset_1('#skF_6', k3_xboole_0('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_353])).
% 4.34/1.88  tff(c_1907, plain, (~r1_tarski(k3_xboole_0('#skF_8', '#skF_7'), '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6')) | ~m1_subset_1(k3_xboole_0('#skF_8', '#skF_7'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_1895, c_354])).
% 4.34/1.88  tff(c_1920, plain, (~m1_subset_1(k3_xboole_0('#skF_8', '#skF_7'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1317, c_1907])).
% 4.34/1.88  tff(c_1929, plain, (~r1_tarski(k3_xboole_0('#skF_8', '#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_551, c_1920])).
% 4.34/1.88  tff(c_1943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1286, c_1929])).
% 4.34/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.34/1.88  
% 4.34/1.88  Inference rules
% 4.34/1.88  ----------------------
% 4.34/1.88  #Ref     : 0
% 4.34/1.88  #Sup     : 445
% 4.34/1.88  #Fact    : 0
% 4.34/1.88  #Define  : 0
% 4.34/1.88  #Split   : 5
% 4.34/1.88  #Chain   : 0
% 4.34/1.88  #Close   : 0
% 4.34/1.88  
% 4.34/1.88  Ordering : KBO
% 4.34/1.88  
% 4.34/1.88  Simplification rules
% 4.34/1.88  ----------------------
% 4.34/1.88  #Subsume      : 90
% 4.34/1.88  #Demod        : 53
% 4.34/1.88  #Tautology    : 78
% 4.34/1.88  #SimpNegUnit  : 28
% 4.34/1.88  #BackRed      : 1
% 4.34/1.88  
% 4.34/1.88  #Partial instantiations: 0
% 4.34/1.88  #Strategies tried      : 1
% 4.34/1.88  
% 4.34/1.88  Timing (in seconds)
% 4.34/1.88  ----------------------
% 4.34/1.89  Preprocessing        : 0.34
% 4.34/1.89  Parsing              : 0.18
% 4.34/1.89  CNF conversion       : 0.03
% 4.34/1.89  Main loop            : 0.70
% 4.34/1.89  Inferencing          : 0.23
% 4.34/1.89  Reduction            : 0.23
% 4.34/1.89  Demodulation         : 0.16
% 4.34/1.89  BG Simplification    : 0.03
% 4.34/1.89  Subsumption          : 0.17
% 4.34/1.89  Abstraction          : 0.04
% 4.34/1.89  MUC search           : 0.00
% 4.34/1.89  Cooper               : 0.00
% 4.34/1.89  Total                : 1.08
% 4.34/1.89  Index Insertion      : 0.00
% 4.34/1.89  Index Deletion       : 0.00
% 4.34/1.89  Index Matching       : 0.00
% 4.34/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
