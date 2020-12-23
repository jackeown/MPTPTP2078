%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:57 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   72 (  99 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :   94 ( 170 expanded)
%              Number of equality atoms :   17 (  34 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_relat_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v3_relat_1,type,(
    v3_relat_1: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( v3_relat_1(A)
        <=> ! [B] :
              ( r2_hidden(B,k2_relat_1(A))
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_relat_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v3_relat_1(A)
      <=> r1_tarski(k2_relat_1(A),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_relat_1)).

tff(f_59,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_46,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v3_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_60,plain,(
    ~ v3_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_119,plain,(
    ! [A_51,C_52,B_53] :
      ( r2_hidden(A_51,C_52)
      | ~ r1_tarski(k2_tarski(A_51,B_53),C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_138,plain,(
    ! [A_54,B_55] : r2_hidden(A_54,k2_tarski(A_54,B_55)) ),
    inference(resolution,[status(thm)],[c_12,c_119])).

tff(c_141,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_138])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [B_34] :
      ( v3_relat_1('#skF_2')
      | k1_xboole_0 = B_34
      | ~ r2_hidden(B_34,k2_relat_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_183,plain,(
    ! [B_62] :
      ( k1_xboole_0 = B_62
      | ~ r2_hidden(B_62,k2_relat_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56])).

tff(c_188,plain,(
    ! [B_2] :
      ( '#skF_1'(k2_relat_1('#skF_2'),B_2) = k1_xboole_0
      | r1_tarski(k2_relat_1('#skF_2'),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_183])).

tff(c_747,plain,(
    ! [A_107] :
      ( v3_relat_1(A_107)
      | ~ r1_tarski(k2_relat_1(A_107),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_751,plain,
    ( v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_188,c_747])).

tff(c_754,plain,
    ( v3_relat_1('#skF_2')
    | '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_751])).

tff(c_755,plain,(
    '#skF_1'(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_754])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_765,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | r1_tarski(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_4])).

tff(c_775,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_765])).

tff(c_40,plain,(
    ! [A_31] :
      ( v3_relat_1(A_31)
      | ~ r1_tarski(k2_relat_1(A_31),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_781,plain,
    ( v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_775,c_40])).

tff(c_789,plain,(
    v3_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_781])).

tff(c_791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_789])).

tff(c_792,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_793,plain,(
    v3_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1218,plain,(
    ! [A_164] :
      ( r1_tarski(k2_relat_1(A_164),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(A_164)
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_48,plain,
    ( r2_hidden('#skF_3',k2_relat_1('#skF_2'))
    | ~ v3_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_794,plain,(
    ~ v3_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_793,c_794])).

tff(c_797,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1059,plain,(
    ! [C_155,B_156,A_157] :
      ( r2_hidden(C_155,B_156)
      | ~ r2_hidden(C_155,A_157)
      | ~ r1_tarski(A_157,B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1095,plain,(
    ! [B_156] :
      ( r2_hidden('#skF_3',B_156)
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_156) ) ),
    inference(resolution,[status(thm)],[c_797,c_1059])).

tff(c_1222,plain,
    ( r2_hidden('#skF_3',k1_tarski(k1_xboole_0))
    | ~ v3_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1218,c_1095])).

tff(c_1230,plain,(
    r2_hidden('#skF_3',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_793,c_1222])).

tff(c_32,plain,(
    ! [A_27] : k3_tarski(k1_tarski(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_841,plain,(
    ! [A_114,B_115] :
      ( r1_tarski(A_114,k3_tarski(B_115))
      | ~ r2_hidden(A_114,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_844,plain,(
    ! [A_114,A_27] :
      ( r1_tarski(A_114,A_27)
      | ~ r2_hidden(A_114,k1_tarski(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_841])).

tff(c_1239,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1230,c_844])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_950,plain,(
    ! [B_140,A_141] :
      ( B_140 = A_141
      | ~ r1_tarski(B_140,A_141)
      | ~ r1_tarski(A_141,B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_968,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_950])).

tff(c_1242,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1239,c_968])).

tff(c_1248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_792,c_1242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.55  
% 3.04/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.55  %$ r2_hidden > r1_tarski > v3_relat_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.04/1.55  
% 3.04/1.55  %Foreground sorts:
% 3.04/1.55  
% 3.04/1.55  
% 3.04/1.55  %Background operators:
% 3.04/1.55  
% 3.04/1.55  
% 3.04/1.55  %Foreground operators:
% 3.04/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.04/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.55  tff(v3_relat_1, type, v3_relat_1: $i > $o).
% 3.04/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.04/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.04/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.04/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.04/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.04/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.04/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.04/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.04/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.04/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.04/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.04/1.55  
% 3.04/1.56  tff(f_81, negated_conjecture, ~(![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> (![B]: (r2_hidden(B, k2_relat_1(A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t184_relat_1)).
% 3.04/1.56  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.04/1.56  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.04/1.56  tff(f_65, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.04/1.56  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.04/1.56  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> r1_tarski(k2_relat_1(A), k1_tarski(k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_relat_1)).
% 3.04/1.56  tff(f_59, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 3.04/1.56  tff(f_54, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.04/1.56  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.04/1.56  tff(c_46, plain, (k1_xboole_0!='#skF_3' | ~v3_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.04/1.56  tff(c_60, plain, (~v3_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 3.04/1.56  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.04/1.56  tff(c_16, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.04/1.56  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.04/1.56  tff(c_119, plain, (![A_51, C_52, B_53]: (r2_hidden(A_51, C_52) | ~r1_tarski(k2_tarski(A_51, B_53), C_52))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.04/1.56  tff(c_138, plain, (![A_54, B_55]: (r2_hidden(A_54, k2_tarski(A_54, B_55)))), inference(resolution, [status(thm)], [c_12, c_119])).
% 3.04/1.56  tff(c_141, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_138])).
% 3.04/1.56  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.04/1.56  tff(c_56, plain, (![B_34]: (v3_relat_1('#skF_2') | k1_xboole_0=B_34 | ~r2_hidden(B_34, k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.04/1.56  tff(c_183, plain, (![B_62]: (k1_xboole_0=B_62 | ~r2_hidden(B_62, k2_relat_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_60, c_56])).
% 3.04/1.56  tff(c_188, plain, (![B_2]: ('#skF_1'(k2_relat_1('#skF_2'), B_2)=k1_xboole_0 | r1_tarski(k2_relat_1('#skF_2'), B_2))), inference(resolution, [status(thm)], [c_6, c_183])).
% 3.04/1.56  tff(c_747, plain, (![A_107]: (v3_relat_1(A_107) | ~r1_tarski(k2_relat_1(A_107), k1_tarski(k1_xboole_0)) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.04/1.56  tff(c_751, plain, (v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | '#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_188, c_747])).
% 3.04/1.56  tff(c_754, plain, (v3_relat_1('#skF_2') | '#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_751])).
% 3.04/1.56  tff(c_755, plain, ('#skF_1'(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_60, c_754])).
% 3.04/1.56  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.04/1.56  tff(c_765, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0)) | r1_tarski(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_755, c_4])).
% 3.04/1.56  tff(c_775, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_765])).
% 3.04/1.56  tff(c_40, plain, (![A_31]: (v3_relat_1(A_31) | ~r1_tarski(k2_relat_1(A_31), k1_tarski(k1_xboole_0)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.04/1.56  tff(c_781, plain, (v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_775, c_40])).
% 3.04/1.56  tff(c_789, plain, (v3_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_781])).
% 3.04/1.56  tff(c_791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_789])).
% 3.04/1.56  tff(c_792, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_46])).
% 3.04/1.56  tff(c_793, plain, (v3_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 3.04/1.56  tff(c_1218, plain, (![A_164]: (r1_tarski(k2_relat_1(A_164), k1_tarski(k1_xboole_0)) | ~v3_relat_1(A_164) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.04/1.56  tff(c_48, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_2')) | ~v3_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.04/1.56  tff(c_794, plain, (~v3_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 3.04/1.56  tff(c_796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_793, c_794])).
% 3.04/1.56  tff(c_797, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_48])).
% 3.04/1.56  tff(c_1059, plain, (![C_155, B_156, A_157]: (r2_hidden(C_155, B_156) | ~r2_hidden(C_155, A_157) | ~r1_tarski(A_157, B_156))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.04/1.56  tff(c_1095, plain, (![B_156]: (r2_hidden('#skF_3', B_156) | ~r1_tarski(k2_relat_1('#skF_2'), B_156))), inference(resolution, [status(thm)], [c_797, c_1059])).
% 3.04/1.56  tff(c_1222, plain, (r2_hidden('#skF_3', k1_tarski(k1_xboole_0)) | ~v3_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1218, c_1095])).
% 3.04/1.56  tff(c_1230, plain, (r2_hidden('#skF_3', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_793, c_1222])).
% 3.04/1.56  tff(c_32, plain, (![A_27]: (k3_tarski(k1_tarski(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.04/1.56  tff(c_841, plain, (![A_114, B_115]: (r1_tarski(A_114, k3_tarski(B_115)) | ~r2_hidden(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.04/1.56  tff(c_844, plain, (![A_114, A_27]: (r1_tarski(A_114, A_27) | ~r2_hidden(A_114, k1_tarski(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_841])).
% 3.04/1.56  tff(c_1239, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_1230, c_844])).
% 3.04/1.56  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.04/1.56  tff(c_950, plain, (![B_140, A_141]: (B_140=A_141 | ~r1_tarski(B_140, A_141) | ~r1_tarski(A_141, B_140))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.04/1.56  tff(c_968, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_950])).
% 3.04/1.56  tff(c_1242, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1239, c_968])).
% 3.04/1.56  tff(c_1248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_792, c_1242])).
% 3.04/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.56  
% 3.04/1.56  Inference rules
% 3.04/1.56  ----------------------
% 3.04/1.56  #Ref     : 0
% 3.04/1.56  #Sup     : 253
% 3.04/1.56  #Fact    : 0
% 3.04/1.56  #Define  : 0
% 3.04/1.56  #Split   : 6
% 3.04/1.56  #Chain   : 0
% 3.04/1.56  #Close   : 0
% 3.04/1.56  
% 3.04/1.56  Ordering : KBO
% 3.04/1.56  
% 3.04/1.56  Simplification rules
% 3.04/1.56  ----------------------
% 3.04/1.56  #Subsume      : 16
% 3.04/1.56  #Demod        : 96
% 3.04/1.56  #Tautology    : 98
% 3.04/1.56  #SimpNegUnit  : 8
% 3.04/1.56  #BackRed      : 4
% 3.04/1.56  
% 3.04/1.56  #Partial instantiations: 0
% 3.04/1.56  #Strategies tried      : 1
% 3.04/1.56  
% 3.04/1.56  Timing (in seconds)
% 3.04/1.56  ----------------------
% 3.04/1.57  Preprocessing        : 0.33
% 3.04/1.57  Parsing              : 0.18
% 3.04/1.57  CNF conversion       : 0.02
% 3.04/1.57  Main loop            : 0.38
% 3.04/1.57  Inferencing          : 0.14
% 3.04/1.57  Reduction            : 0.12
% 3.04/1.57  Demodulation         : 0.09
% 3.04/1.57  BG Simplification    : 0.02
% 3.04/1.57  Subsumption          : 0.07
% 3.04/1.57  Abstraction          : 0.02
% 3.04/1.57  MUC search           : 0.00
% 3.04/1.57  Cooper               : 0.00
% 3.04/1.57  Total                : 0.74
% 3.04/1.57  Index Insertion      : 0.00
% 3.04/1.57  Index Deletion       : 0.00
% 3.04/1.57  Index Matching       : 0.00
% 3.04/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
