%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:47 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 107 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 194 expanded)
%              Number of equality atoms :   23 (  57 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_63,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_34,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_617,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_2'(A_90,B_91),B_91)
      | r2_hidden('#skF_3'(A_90,B_91),A_90)
      | B_91 = A_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [A_18] : k3_xboole_0(A_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_137,plain,(
    ! [A_31,B_32,C_33] :
      ( ~ r1_xboole_0(A_31,B_32)
      | ~ r2_hidden(C_33,k3_xboole_0(A_31,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_149,plain,(
    ! [A_18,C_33] :
      ( ~ r1_xboole_0(A_18,k1_xboole_0)
      | ~ r2_hidden(C_33,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_137])).

tff(c_151,plain,(
    ! [C_33] : ~ r2_hidden(C_33,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_149])).

tff(c_656,plain,(
    ! [B_91] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_91),B_91)
      | k1_xboole_0 = B_91 ) ),
    inference(resolution,[status(thm)],[c_617,c_151])).

tff(c_877,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( r2_hidden(k4_tarski(A_107,B_108),k2_zfmisc_1(C_109,D_110))
      | ~ r2_hidden(B_108,D_110)
      | ~ r2_hidden(A_107,C_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_40,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_371,plain,(
    ! [A_70,C_71,B_72,D_73] :
      ( r2_hidden(A_70,C_71)
      | ~ r2_hidden(k4_tarski(A_70,B_72),k2_zfmisc_1(C_71,D_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_374,plain,(
    ! [A_70,B_72] :
      ( r2_hidden(A_70,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_70,B_72),k2_zfmisc_1('#skF_6','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_371])).

tff(c_897,plain,(
    ! [A_107,B_108] :
      ( r2_hidden(A_107,'#skF_5')
      | ~ r2_hidden(B_108,'#skF_5')
      | ~ r2_hidden(A_107,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_877,c_374])).

tff(c_904,plain,(
    ! [B_111] : ~ r2_hidden(B_111,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_897])).

tff(c_916,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_656,c_904])).

tff(c_936,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_916])).

tff(c_938,plain,(
    ! [A_112] :
      ( r2_hidden(A_112,'#skF_5')
      | ~ r2_hidden(A_112,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_897])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_956,plain,(
    ! [A_113] :
      ( r1_tarski(A_113,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_113,'#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_938,c_6])).

tff(c_961,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_956])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_965,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_961,c_22])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1076,plain,(
    ! [A_120,B_121] :
      ( r2_hidden(k4_tarski(A_120,B_121),k2_zfmisc_1('#skF_6','#skF_5'))
      | ~ r2_hidden(B_121,'#skF_6')
      | ~ r2_hidden(A_120,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_877])).

tff(c_32,plain,(
    ! [A_20,C_22,B_21,D_23] :
      ( r2_hidden(A_20,C_22)
      | ~ r2_hidden(k4_tarski(A_20,B_21),k2_zfmisc_1(C_22,D_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1092,plain,(
    ! [A_120,B_121] :
      ( r2_hidden(A_120,'#skF_6')
      | ~ r2_hidden(B_121,'#skF_6')
      | ~ r2_hidden(A_120,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1076,c_32])).

tff(c_1119,plain,(
    ! [B_125] : ~ r2_hidden(B_125,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1092])).

tff(c_1139,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_656,c_1119])).

tff(c_1161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1139])).

tff(c_1163,plain,(
    ! [A_126] :
      ( r2_hidden(A_126,'#skF_6')
      | ~ r2_hidden(A_126,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_1092])).

tff(c_1572,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_1'('#skF_5',B_142),'#skF_6')
      | r1_tarski('#skF_5',B_142) ) ),
    inference(resolution,[status(thm)],[c_8,c_1163])).

tff(c_1590,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1572,c_6])).

tff(c_1630,plain,(
    k3_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1590,c_22])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1688,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1630,c_2])).

tff(c_1721,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_1688])).

tff(c_1723,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1721])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:58:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.60  
% 3.40/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.60  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 3.40/1.60  
% 3.40/1.60  %Foreground sorts:
% 3.40/1.60  
% 3.40/1.60  
% 3.40/1.60  %Background operators:
% 3.40/1.60  
% 3.40/1.60  
% 3.40/1.60  %Foreground operators:
% 3.40/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.60  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.40/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.60  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.40/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.40/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.40/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.40/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.40/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.40/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.40/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.40/1.60  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.40/1.60  
% 3.40/1.61  tff(f_78, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 3.40/1.61  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.40/1.61  tff(f_41, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.40/1.61  tff(f_63, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.40/1.61  tff(f_61, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.40/1.61  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.40/1.61  tff(f_69, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.40/1.61  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.40/1.61  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.40/1.61  tff(c_34, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.40/1.61  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.40/1.61  tff(c_38, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.40/1.61  tff(c_617, plain, (![A_90, B_91]: (r2_hidden('#skF_2'(A_90, B_91), B_91) | r2_hidden('#skF_3'(A_90, B_91), A_90) | B_91=A_90)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.40/1.61  tff(c_26, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.40/1.61  tff(c_24, plain, (![A_18]: (k3_xboole_0(A_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.40/1.61  tff(c_137, plain, (![A_31, B_32, C_33]: (~r1_xboole_0(A_31, B_32) | ~r2_hidden(C_33, k3_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.40/1.61  tff(c_149, plain, (![A_18, C_33]: (~r1_xboole_0(A_18, k1_xboole_0) | ~r2_hidden(C_33, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_137])).
% 3.40/1.61  tff(c_151, plain, (![C_33]: (~r2_hidden(C_33, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_149])).
% 3.40/1.61  tff(c_656, plain, (![B_91]: (r2_hidden('#skF_2'(k1_xboole_0, B_91), B_91) | k1_xboole_0=B_91)), inference(resolution, [status(thm)], [c_617, c_151])).
% 3.40/1.61  tff(c_877, plain, (![A_107, B_108, C_109, D_110]: (r2_hidden(k4_tarski(A_107, B_108), k2_zfmisc_1(C_109, D_110)) | ~r2_hidden(B_108, D_110) | ~r2_hidden(A_107, C_109))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.40/1.61  tff(c_40, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.40/1.61  tff(c_371, plain, (![A_70, C_71, B_72, D_73]: (r2_hidden(A_70, C_71) | ~r2_hidden(k4_tarski(A_70, B_72), k2_zfmisc_1(C_71, D_73)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.40/1.61  tff(c_374, plain, (![A_70, B_72]: (r2_hidden(A_70, '#skF_5') | ~r2_hidden(k4_tarski(A_70, B_72), k2_zfmisc_1('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_40, c_371])).
% 3.40/1.61  tff(c_897, plain, (![A_107, B_108]: (r2_hidden(A_107, '#skF_5') | ~r2_hidden(B_108, '#skF_5') | ~r2_hidden(A_107, '#skF_6'))), inference(resolution, [status(thm)], [c_877, c_374])).
% 3.40/1.61  tff(c_904, plain, (![B_111]: (~r2_hidden(B_111, '#skF_5'))), inference(splitLeft, [status(thm)], [c_897])).
% 3.40/1.61  tff(c_916, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_656, c_904])).
% 3.40/1.61  tff(c_936, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_916])).
% 3.40/1.61  tff(c_938, plain, (![A_112]: (r2_hidden(A_112, '#skF_5') | ~r2_hidden(A_112, '#skF_6'))), inference(splitRight, [status(thm)], [c_897])).
% 3.40/1.61  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.40/1.61  tff(c_956, plain, (![A_113]: (r1_tarski(A_113, '#skF_5') | ~r2_hidden('#skF_1'(A_113, '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_938, c_6])).
% 3.40/1.61  tff(c_961, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_8, c_956])).
% 3.40/1.61  tff(c_22, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.40/1.61  tff(c_965, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_961, c_22])).
% 3.40/1.61  tff(c_36, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.40/1.61  tff(c_1076, plain, (![A_120, B_121]: (r2_hidden(k4_tarski(A_120, B_121), k2_zfmisc_1('#skF_6', '#skF_5')) | ~r2_hidden(B_121, '#skF_6') | ~r2_hidden(A_120, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_877])).
% 3.40/1.61  tff(c_32, plain, (![A_20, C_22, B_21, D_23]: (r2_hidden(A_20, C_22) | ~r2_hidden(k4_tarski(A_20, B_21), k2_zfmisc_1(C_22, D_23)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.40/1.61  tff(c_1092, plain, (![A_120, B_121]: (r2_hidden(A_120, '#skF_6') | ~r2_hidden(B_121, '#skF_6') | ~r2_hidden(A_120, '#skF_5'))), inference(resolution, [status(thm)], [c_1076, c_32])).
% 3.40/1.61  tff(c_1119, plain, (![B_125]: (~r2_hidden(B_125, '#skF_6'))), inference(splitLeft, [status(thm)], [c_1092])).
% 3.40/1.61  tff(c_1139, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_656, c_1119])).
% 3.40/1.61  tff(c_1161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_1139])).
% 3.40/1.61  tff(c_1163, plain, (![A_126]: (r2_hidden(A_126, '#skF_6') | ~r2_hidden(A_126, '#skF_5'))), inference(splitRight, [status(thm)], [c_1092])).
% 3.40/1.61  tff(c_1572, plain, (![B_142]: (r2_hidden('#skF_1'('#skF_5', B_142), '#skF_6') | r1_tarski('#skF_5', B_142))), inference(resolution, [status(thm)], [c_8, c_1163])).
% 3.40/1.61  tff(c_1590, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1572, c_6])).
% 3.40/1.61  tff(c_1630, plain, (k3_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_1590, c_22])).
% 3.40/1.61  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.40/1.61  tff(c_1688, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1630, c_2])).
% 3.40/1.61  tff(c_1721, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_965, c_1688])).
% 3.40/1.61  tff(c_1723, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1721])).
% 3.40/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.61  
% 3.40/1.61  Inference rules
% 3.40/1.61  ----------------------
% 3.40/1.61  #Ref     : 0
% 3.40/1.61  #Sup     : 380
% 3.40/1.61  #Fact    : 0
% 3.40/1.61  #Define  : 0
% 3.40/1.61  #Split   : 5
% 3.40/1.61  #Chain   : 0
% 3.40/1.61  #Close   : 0
% 3.40/1.61  
% 3.40/1.61  Ordering : KBO
% 3.40/1.61  
% 3.40/1.61  Simplification rules
% 3.40/1.61  ----------------------
% 3.40/1.61  #Subsume      : 134
% 3.40/1.61  #Demod        : 148
% 3.40/1.61  #Tautology    : 94
% 3.40/1.61  #SimpNegUnit  : 26
% 3.40/1.61  #BackRed      : 2
% 3.40/1.61  
% 3.40/1.61  #Partial instantiations: 0
% 3.40/1.61  #Strategies tried      : 1
% 3.40/1.61  
% 3.40/1.61  Timing (in seconds)
% 3.40/1.61  ----------------------
% 3.40/1.62  Preprocessing        : 0.31
% 3.40/1.62  Parsing              : 0.17
% 3.40/1.62  CNF conversion       : 0.02
% 3.40/1.62  Main loop            : 0.49
% 3.40/1.62  Inferencing          : 0.18
% 3.40/1.62  Reduction            : 0.16
% 3.40/1.62  Demodulation         : 0.11
% 3.40/1.62  BG Simplification    : 0.02
% 3.40/1.62  Subsumption          : 0.11
% 3.40/1.62  Abstraction          : 0.02
% 3.40/1.62  MUC search           : 0.00
% 3.40/1.62  Cooper               : 0.00
% 3.40/1.62  Total                : 0.83
% 3.40/1.62  Index Insertion      : 0.00
% 3.40/1.62  Index Deletion       : 0.00
% 3.40/1.62  Index Matching       : 0.00
% 3.40/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
