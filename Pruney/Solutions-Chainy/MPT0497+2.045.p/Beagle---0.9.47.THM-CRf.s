%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:45 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   67 (  86 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  106 ( 152 expanded)
%              Number of equality atoms :   24 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_51,axiom,(
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

tff(f_71,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_81,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(c_52,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_92,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_123,plain,(
    k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_46])).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_40,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_25,A_24)),A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    ! [B_27,A_26] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_27,A_26)),k1_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_947,plain,(
    ! [A_136,C_137,B_138] :
      ( r1_xboole_0(A_136,C_137)
      | ~ r1_xboole_0(B_138,C_137)
      | ~ r1_tarski(A_136,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_989,plain,(
    ! [A_143] :
      ( r1_xboole_0(A_143,'#skF_2')
      | ~ r1_tarski(A_143,k1_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_92,c_947])).

tff(c_997,plain,(
    ! [A_26] :
      ( r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3',A_26)),'#skF_2')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_989])).

tff(c_1022,plain,(
    ! [A_145] : r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3',A_145)),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_997])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( ~ r1_xboole_0(B_13,A_12)
      | ~ r1_tarski(B_13,A_12)
      | v1_xboole_0(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1829,plain,(
    ! [A_203] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_203)),'#skF_2')
      | v1_xboole_0(k1_relat_1(k7_relat_1('#skF_3',A_203))) ) ),
    inference(resolution,[status(thm)],[c_1022,c_14])).

tff(c_1844,plain,
    ( v1_xboole_0(k1_relat_1(k7_relat_1('#skF_3','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1829])).

tff(c_1853,plain,(
    v1_xboole_0(k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1844])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1860,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1853,c_2])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( v1_relat_1(k7_relat_1(A_18,B_19))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_102,plain,(
    ! [A_38] :
      ( k1_relat_1(A_38) != k1_xboole_0
      | k1_xboole_0 = A_38
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_109,plain,(
    ! [A_18,B_19] :
      ( k1_relat_1(k7_relat_1(A_18,B_19)) != k1_xboole_0
      | k7_relat_1(A_18,B_19) = k1_xboole_0
      | ~ v1_relat_1(A_18) ) ),
    inference(resolution,[status(thm)],[c_24,c_102])).

tff(c_1897,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1860,c_109])).

tff(c_1945,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1897])).

tff(c_1947,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_1945])).

tff(c_1949,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),B_5)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),A_4)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_84,plain,(
    ! [A_31,B_32] : ~ r2_hidden(A_31,k2_zfmisc_1(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_90,plain,(
    ! [A_14] : ~ r2_hidden(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_84])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1948,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2330,plain,(
    ! [A_261,C_262,B_263] :
      ( r2_hidden(A_261,k1_relat_1(k7_relat_1(C_262,B_263)))
      | ~ r2_hidden(A_261,k1_relat_1(C_262))
      | ~ r2_hidden(A_261,B_263)
      | ~ v1_relat_1(C_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2349,plain,(
    ! [A_261] :
      ( r2_hidden(A_261,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_261,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_261,'#skF_2')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1948,c_2330])).

tff(c_2359,plain,(
    ! [A_261] :
      ( r2_hidden(A_261,k1_xboole_0)
      | ~ r2_hidden(A_261,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_261,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_28,c_2349])).

tff(c_2361,plain,(
    ! [A_264] :
      ( ~ r2_hidden(A_264,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_264,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_2359])).

tff(c_2372,plain,(
    ! [B_265] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1('#skF_3'),B_265),'#skF_2')
      | r1_xboole_0(k1_relat_1('#skF_3'),B_265) ) ),
    inference(resolution,[status(thm)],[c_10,c_2361])).

tff(c_2376,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_2372])).

tff(c_2380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1949,c_1949,c_2376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:47:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.58  
% 3.56/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.59  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.56/1.59  
% 3.56/1.59  %Foreground sorts:
% 3.56/1.59  
% 3.56/1.59  
% 3.56/1.59  %Background operators:
% 3.56/1.59  
% 3.56/1.59  
% 3.56/1.59  %Foreground operators:
% 3.56/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.56/1.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.56/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.56/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.56/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.56/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.56/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.56/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.56/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.56/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.56/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.56/1.59  
% 3.56/1.60  tff(f_112, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.56/1.60  tff(f_101, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 3.56/1.60  tff(f_105, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 3.56/1.60  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.56/1.60  tff(f_65, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.56/1.60  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.56/1.60  tff(f_78, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.56/1.60  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.56/1.60  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.56/1.60  tff(f_71, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.56/1.60  tff(f_74, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.56/1.60  tff(f_81, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.56/1.60  tff(f_97, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 3.56/1.60  tff(c_52, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.56/1.60  tff(c_92, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 3.56/1.60  tff(c_46, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.56/1.60  tff(c_123, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_92, c_46])).
% 3.56/1.60  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.56/1.60  tff(c_40, plain, (![B_25, A_24]: (r1_tarski(k1_relat_1(k7_relat_1(B_25, A_24)), A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.56/1.60  tff(c_42, plain, (![B_27, A_26]: (r1_tarski(k1_relat_1(k7_relat_1(B_27, A_26)), k1_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.56/1.60  tff(c_947, plain, (![A_136, C_137, B_138]: (r1_xboole_0(A_136, C_137) | ~r1_xboole_0(B_138, C_137) | ~r1_tarski(A_136, B_138))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.56/1.60  tff(c_989, plain, (![A_143]: (r1_xboole_0(A_143, '#skF_2') | ~r1_tarski(A_143, k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_92, c_947])).
% 3.56/1.60  tff(c_997, plain, (![A_26]: (r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3', A_26)), '#skF_2') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_989])).
% 3.56/1.60  tff(c_1022, plain, (![A_145]: (r1_xboole_0(k1_relat_1(k7_relat_1('#skF_3', A_145)), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_997])).
% 3.56/1.60  tff(c_14, plain, (![B_13, A_12]: (~r1_xboole_0(B_13, A_12) | ~r1_tarski(B_13, A_12) | v1_xboole_0(B_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.56/1.60  tff(c_1829, plain, (![A_203]: (~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_203)), '#skF_2') | v1_xboole_0(k1_relat_1(k7_relat_1('#skF_3', A_203))))), inference(resolution, [status(thm)], [c_1022, c_14])).
% 3.56/1.60  tff(c_1844, plain, (v1_xboole_0(k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_1829])).
% 3.56/1.60  tff(c_1853, plain, (v1_xboole_0(k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1844])).
% 3.56/1.60  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.56/1.60  tff(c_1860, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1853, c_2])).
% 3.56/1.60  tff(c_24, plain, (![A_18, B_19]: (v1_relat_1(k7_relat_1(A_18, B_19)) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.56/1.60  tff(c_102, plain, (![A_38]: (k1_relat_1(A_38)!=k1_xboole_0 | k1_xboole_0=A_38 | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.56/1.60  tff(c_109, plain, (![A_18, B_19]: (k1_relat_1(k7_relat_1(A_18, B_19))!=k1_xboole_0 | k7_relat_1(A_18, B_19)=k1_xboole_0 | ~v1_relat_1(A_18))), inference(resolution, [status(thm)], [c_24, c_102])).
% 3.56/1.60  tff(c_1897, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1860, c_109])).
% 3.56/1.60  tff(c_1945, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1897])).
% 3.56/1.60  tff(c_1947, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_1945])).
% 3.56/1.60  tff(c_1949, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 3.56/1.60  tff(c_8, plain, (![A_4, B_5]: (r2_hidden('#skF_1'(A_4, B_5), B_5) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.56/1.60  tff(c_10, plain, (![A_4, B_5]: (r2_hidden('#skF_1'(A_4, B_5), A_4) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.56/1.60  tff(c_18, plain, (![A_14]: (k2_zfmisc_1(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.56/1.60  tff(c_84, plain, (![A_31, B_32]: (~r2_hidden(A_31, k2_zfmisc_1(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.56/1.60  tff(c_90, plain, (![A_14]: (~r2_hidden(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_84])).
% 3.56/1.60  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.56/1.60  tff(c_1948, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.56/1.60  tff(c_2330, plain, (![A_261, C_262, B_263]: (r2_hidden(A_261, k1_relat_1(k7_relat_1(C_262, B_263))) | ~r2_hidden(A_261, k1_relat_1(C_262)) | ~r2_hidden(A_261, B_263) | ~v1_relat_1(C_262))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.56/1.60  tff(c_2349, plain, (![A_261]: (r2_hidden(A_261, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_261, k1_relat_1('#skF_3')) | ~r2_hidden(A_261, '#skF_2') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1948, c_2330])).
% 3.56/1.60  tff(c_2359, plain, (![A_261]: (r2_hidden(A_261, k1_xboole_0) | ~r2_hidden(A_261, k1_relat_1('#skF_3')) | ~r2_hidden(A_261, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_28, c_2349])).
% 3.56/1.60  tff(c_2361, plain, (![A_264]: (~r2_hidden(A_264, k1_relat_1('#skF_3')) | ~r2_hidden(A_264, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_90, c_2359])).
% 3.56/1.60  tff(c_2372, plain, (![B_265]: (~r2_hidden('#skF_1'(k1_relat_1('#skF_3'), B_265), '#skF_2') | r1_xboole_0(k1_relat_1('#skF_3'), B_265))), inference(resolution, [status(thm)], [c_10, c_2361])).
% 3.56/1.60  tff(c_2376, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_8, c_2372])).
% 3.56/1.60  tff(c_2380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1949, c_1949, c_2376])).
% 3.56/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.60  
% 3.56/1.60  Inference rules
% 3.56/1.60  ----------------------
% 3.56/1.60  #Ref     : 0
% 3.56/1.60  #Sup     : 511
% 3.56/1.60  #Fact    : 0
% 3.56/1.60  #Define  : 0
% 3.56/1.60  #Split   : 18
% 3.56/1.60  #Chain   : 0
% 3.56/1.60  #Close   : 0
% 3.56/1.60  
% 3.56/1.60  Ordering : KBO
% 3.56/1.60  
% 3.56/1.60  Simplification rules
% 3.56/1.60  ----------------------
% 3.56/1.60  #Subsume      : 96
% 3.56/1.60  #Demod        : 341
% 3.56/1.60  #Tautology    : 187
% 3.56/1.60  #SimpNegUnit  : 25
% 3.56/1.60  #BackRed      : 7
% 3.56/1.60  
% 3.56/1.60  #Partial instantiations: 0
% 3.56/1.60  #Strategies tried      : 1
% 3.56/1.60  
% 3.56/1.60  Timing (in seconds)
% 3.56/1.60  ----------------------
% 3.56/1.60  Preprocessing        : 0.29
% 3.56/1.60  Parsing              : 0.16
% 3.56/1.60  CNF conversion       : 0.02
% 3.56/1.60  Main loop            : 0.55
% 3.56/1.60  Inferencing          : 0.21
% 3.56/1.60  Reduction            : 0.16
% 3.56/1.60  Demodulation         : 0.11
% 3.56/1.60  BG Simplification    : 0.02
% 3.56/1.60  Subsumption          : 0.12
% 3.56/1.60  Abstraction          : 0.02
% 3.56/1.60  MUC search           : 0.00
% 3.56/1.60  Cooper               : 0.00
% 3.56/1.60  Total                : 0.88
% 3.56/1.60  Index Insertion      : 0.00
% 3.56/1.60  Index Deletion       : 0.00
% 3.56/1.60  Index Matching       : 0.00
% 3.56/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
