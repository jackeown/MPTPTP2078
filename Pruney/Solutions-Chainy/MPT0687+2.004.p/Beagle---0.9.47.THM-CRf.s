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
% DateTime   : Thu Dec  3 10:04:33 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   53 (  68 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   79 ( 126 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_75,plain,(
    ~ r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,
    ( r2_hidden('#skF_2',k2_relat_1('#skF_3'))
    | k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_100,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_38])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(k1_tarski(A_11),B_12)
      | r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_106,plain,(
    ! [A_43,B_44,C_45] :
      ( ~ r1_xboole_0(A_43,B_44)
      | ~ r2_hidden(C_45,B_44)
      | ~ r2_hidden(C_45,A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_119,plain,(
    ! [C_50,B_51,A_52] :
      ( ~ r2_hidden(C_50,B_51)
      | ~ r2_hidden(C_50,k1_tarski(A_52))
      | r2_hidden(A_52,B_51) ) ),
    inference(resolution,[status(thm)],[c_18,c_106])).

tff(c_269,plain,(
    ! [A_75,B_76,A_77] :
      ( ~ r2_hidden('#skF_1'(A_75,B_76),k1_tarski(A_77))
      | r2_hidden(A_77,A_75)
      | r1_xboole_0(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_6,c_119])).

tff(c_296,plain,(
    ! [A_78,A_79] :
      ( r2_hidden(A_78,A_79)
      | r1_xboole_0(A_79,k1_tarski(A_78)) ) ),
    inference(resolution,[status(thm)],[c_4,c_269])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( k10_relat_1(B_17,A_16) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_323,plain,(
    ! [B_83,A_84] :
      ( k10_relat_1(B_83,k1_tarski(A_84)) = k1_xboole_0
      | ~ v1_relat_1(B_83)
      | r2_hidden(A_84,k2_relat_1(B_83)) ) ),
    inference(resolution,[status(thm)],[c_296,c_26])).

tff(c_326,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_323,c_75])).

tff(c_329,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_326])).

tff(c_331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_329])).

tff(c_332,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_333,plain,(
    r2_hidden('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_14,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_61,plain,(
    ! [B_26,C_27,A_28] :
      ( r2_hidden(B_26,C_27)
      | ~ r1_tarski(k2_tarski(A_28,B_26),C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_70,plain,(
    ! [B_29,A_30] : r2_hidden(B_29,k2_tarski(A_30,B_29)) ),
    inference(resolution,[status(thm)],[c_12,c_61])).

tff(c_73,plain,(
    ! [A_8] : r2_hidden(A_8,k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_70])).

tff(c_374,plain,(
    ! [B_101,A_102] :
      ( r1_xboole_0(k2_relat_1(B_101),A_102)
      | k10_relat_1(B_101,A_102) != k1_xboole_0
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_522,plain,(
    ! [C_126,A_127,B_128] :
      ( ~ r2_hidden(C_126,A_127)
      | ~ r2_hidden(C_126,k2_relat_1(B_128))
      | k10_relat_1(B_128,A_127) != k1_xboole_0
      | ~ v1_relat_1(B_128) ) ),
    inference(resolution,[status(thm)],[c_374,c_2])).

tff(c_554,plain,(
    ! [A_130,B_131] :
      ( ~ r2_hidden(A_130,k2_relat_1(B_131))
      | k10_relat_1(B_131,k1_tarski(A_130)) != k1_xboole_0
      | ~ v1_relat_1(B_131) ) ),
    inference(resolution,[status(thm)],[c_73,c_522])).

tff(c_561,plain,
    ( k10_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_333,c_554])).

tff(c_570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_332,c_561])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.41  
% 2.71/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.71/1.41  
% 2.71/1.41  %Foreground sorts:
% 2.71/1.41  
% 2.71/1.41  
% 2.71/1.41  %Background operators:
% 2.71/1.41  
% 2.71/1.41  
% 2.71/1.41  %Foreground operators:
% 2.71/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.71/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.71/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.71/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.71/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.41  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.71/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.71/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.71/1.41  
% 2.71/1.43  tff(f_78, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.71/1.43  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.71/1.43  tff(f_58, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.71/1.43  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.71/1.43  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.71/1.43  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.71/1.43  tff(f_64, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.71/1.43  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.71/1.43  tff(c_32, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.71/1.43  tff(c_75, plain, (~r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_32])).
% 2.71/1.43  tff(c_38, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3')) | k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.71/1.43  tff(c_100, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_75, c_38])).
% 2.71/1.43  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.71/1.43  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.71/1.43  tff(c_18, plain, (![A_11, B_12]: (r1_xboole_0(k1_tarski(A_11), B_12) | r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.71/1.43  tff(c_106, plain, (![A_43, B_44, C_45]: (~r1_xboole_0(A_43, B_44) | ~r2_hidden(C_45, B_44) | ~r2_hidden(C_45, A_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.71/1.43  tff(c_119, plain, (![C_50, B_51, A_52]: (~r2_hidden(C_50, B_51) | ~r2_hidden(C_50, k1_tarski(A_52)) | r2_hidden(A_52, B_51))), inference(resolution, [status(thm)], [c_18, c_106])).
% 2.71/1.43  tff(c_269, plain, (![A_75, B_76, A_77]: (~r2_hidden('#skF_1'(A_75, B_76), k1_tarski(A_77)) | r2_hidden(A_77, A_75) | r1_xboole_0(A_75, B_76))), inference(resolution, [status(thm)], [c_6, c_119])).
% 2.71/1.43  tff(c_296, plain, (![A_78, A_79]: (r2_hidden(A_78, A_79) | r1_xboole_0(A_79, k1_tarski(A_78)))), inference(resolution, [status(thm)], [c_4, c_269])).
% 2.71/1.43  tff(c_26, plain, (![B_17, A_16]: (k10_relat_1(B_17, A_16)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.71/1.43  tff(c_323, plain, (![B_83, A_84]: (k10_relat_1(B_83, k1_tarski(A_84))=k1_xboole_0 | ~v1_relat_1(B_83) | r2_hidden(A_84, k2_relat_1(B_83)))), inference(resolution, [status(thm)], [c_296, c_26])).
% 2.71/1.43  tff(c_326, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_323, c_75])).
% 2.71/1.43  tff(c_329, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_326])).
% 2.71/1.43  tff(c_331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_329])).
% 2.71/1.43  tff(c_332, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.71/1.43  tff(c_333, plain, (r2_hidden('#skF_2', k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_32])).
% 2.71/1.43  tff(c_14, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.71/1.43  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.71/1.43  tff(c_61, plain, (![B_26, C_27, A_28]: (r2_hidden(B_26, C_27) | ~r1_tarski(k2_tarski(A_28, B_26), C_27))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.71/1.43  tff(c_70, plain, (![B_29, A_30]: (r2_hidden(B_29, k2_tarski(A_30, B_29)))), inference(resolution, [status(thm)], [c_12, c_61])).
% 2.71/1.43  tff(c_73, plain, (![A_8]: (r2_hidden(A_8, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_70])).
% 2.71/1.43  tff(c_374, plain, (![B_101, A_102]: (r1_xboole_0(k2_relat_1(B_101), A_102) | k10_relat_1(B_101, A_102)!=k1_xboole_0 | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.71/1.43  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.71/1.43  tff(c_522, plain, (![C_126, A_127, B_128]: (~r2_hidden(C_126, A_127) | ~r2_hidden(C_126, k2_relat_1(B_128)) | k10_relat_1(B_128, A_127)!=k1_xboole_0 | ~v1_relat_1(B_128))), inference(resolution, [status(thm)], [c_374, c_2])).
% 2.71/1.43  tff(c_554, plain, (![A_130, B_131]: (~r2_hidden(A_130, k2_relat_1(B_131)) | k10_relat_1(B_131, k1_tarski(A_130))!=k1_xboole_0 | ~v1_relat_1(B_131))), inference(resolution, [status(thm)], [c_73, c_522])).
% 2.71/1.43  tff(c_561, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_333, c_554])).
% 2.71/1.43  tff(c_570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_332, c_561])).
% 2.71/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.43  
% 2.71/1.43  Inference rules
% 2.71/1.43  ----------------------
% 2.71/1.43  #Ref     : 0
% 2.71/1.43  #Sup     : 121
% 2.71/1.43  #Fact    : 0
% 2.71/1.43  #Define  : 0
% 2.71/1.43  #Split   : 1
% 2.71/1.43  #Chain   : 0
% 2.71/1.43  #Close   : 0
% 2.71/1.43  
% 2.71/1.43  Ordering : KBO
% 2.71/1.43  
% 2.71/1.43  Simplification rules
% 2.71/1.43  ----------------------
% 2.71/1.43  #Subsume      : 10
% 2.71/1.43  #Demod        : 24
% 2.71/1.43  #Tautology    : 36
% 2.71/1.43  #SimpNegUnit  : 2
% 2.71/1.43  #BackRed      : 0
% 2.71/1.43  
% 2.71/1.43  #Partial instantiations: 0
% 2.71/1.43  #Strategies tried      : 1
% 2.71/1.43  
% 2.71/1.43  Timing (in seconds)
% 2.71/1.43  ----------------------
% 2.71/1.43  Preprocessing        : 0.31
% 2.71/1.43  Parsing              : 0.16
% 2.71/1.43  CNF conversion       : 0.02
% 2.71/1.43  Main loop            : 0.34
% 2.71/1.43  Inferencing          : 0.13
% 2.71/1.43  Reduction            : 0.09
% 2.71/1.43  Demodulation         : 0.07
% 2.71/1.43  BG Simplification    : 0.02
% 2.71/1.43  Subsumption          : 0.08
% 2.71/1.43  Abstraction          : 0.02
% 2.71/1.43  MUC search           : 0.00
% 2.71/1.43  Cooper               : 0.00
% 2.71/1.43  Total                : 0.68
% 2.71/1.43  Index Insertion      : 0.00
% 2.71/1.43  Index Deletion       : 0.00
% 2.71/1.43  Index Matching       : 0.00
% 2.71/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
