%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:41 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 107 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  127 ( 432 expanded)
%              Number of equality atoms :   40 ( 165 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( ( k1_relat_1(B) = A
                & k1_relat_1(C) = A
                & r1_tarski(k2_relat_1(C),A)
                & v2_funct_1(B)
                & k5_relat_1(C,B) = B )
             => C = k6_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,k6_relat_1(B))))
      <=> ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(c_30,plain,(
    k6_relat_1('#skF_4') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_44,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_38,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_221,plain,(
    ! [B_43] :
      ( k1_funct_1(B_43,'#skF_3'(k1_relat_1(B_43),B_43)) != '#skF_3'(k1_relat_1(B_43),B_43)
      | k6_relat_1(k1_relat_1(B_43)) = B_43
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_224,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4','#skF_6')) != '#skF_3'(k1_relat_1('#skF_6'),'#skF_6')
    | k6_relat_1(k1_relat_1('#skF_6')) = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_221])).

tff(c_229,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4','#skF_6')) != '#skF_3'('#skF_4','#skF_6')
    | k6_relat_1('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_38,c_224])).

tff(c_230,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_4','#skF_6')) != '#skF_3'('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_229])).

tff(c_107,plain,(
    ! [B_32] :
      ( r2_hidden('#skF_3'(k1_relat_1(B_32),B_32),k1_relat_1(B_32))
      | k6_relat_1(k1_relat_1(B_32)) = B_32
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_110,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_6'),k1_relat_1('#skF_6'))
    | k6_relat_1(k1_relat_1('#skF_6')) = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_107])).

tff(c_121,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_6'),'#skF_4')
    | k6_relat_1('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_38,c_110])).

tff(c_122,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_121])).

tff(c_36,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_86,plain,(
    ! [B_27,A_28] :
      ( k5_relat_1(B_27,k6_relat_1(A_28)) = B_27
      | ~ r1_tarski(k2_relat_1(B_27),A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,
    ( k5_relat_1('#skF_6',k6_relat_1('#skF_4')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_86])).

tff(c_92,plain,(
    k5_relat_1('#skF_6',k6_relat_1('#skF_4')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_89])).

tff(c_193,plain,(
    ! [C_39,A_40,B_41] :
      ( r2_hidden(k1_funct_1(C_39,A_40),B_41)
      | ~ r2_hidden(A_40,k1_relat_1(k5_relat_1(C_39,k6_relat_1(B_41))))
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_200,plain,(
    ! [A_40] :
      ( r2_hidden(k1_funct_1('#skF_6',A_40),'#skF_4')
      | ~ r2_hidden(A_40,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_193])).

tff(c_211,plain,(
    ! [A_40] :
      ( r2_hidden(k1_funct_1('#skF_6',A_40),'#skF_4')
      | ~ r2_hidden(A_40,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_200])).

tff(c_48,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_34,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_40,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_32,plain,(
    k5_relat_1('#skF_6','#skF_5') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_257,plain,(
    ! [C_50,B_51,A_52] :
      ( k1_funct_1(k5_relat_1(C_50,B_51),A_52) = k1_funct_1(B_51,k1_funct_1(C_50,A_52))
      | ~ r2_hidden(A_52,k1_relat_1(k5_relat_1(C_50,B_51)))
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50)
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_278,plain,(
    ! [A_52] :
      ( k1_funct_1(k5_relat_1('#skF_6','#skF_5'),A_52) = k1_funct_1('#skF_5',k1_funct_1('#skF_6',A_52))
      | ~ r2_hidden(A_52,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_257])).

tff(c_287,plain,(
    ! [A_53] :
      ( k1_funct_1('#skF_5',k1_funct_1('#skF_6',A_53)) = k1_funct_1('#skF_5',A_53)
      | ~ r2_hidden(A_53,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_32,c_278])).

tff(c_4,plain,(
    ! [C_9,B_8,A_3] :
      ( C_9 = B_8
      | k1_funct_1(A_3,C_9) != k1_funct_1(A_3,B_8)
      | ~ r2_hidden(C_9,k1_relat_1(A_3))
      | ~ r2_hidden(B_8,k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_292,plain,(
    ! [A_53,B_8] :
      ( k1_funct_1('#skF_6',A_53) = B_8
      | k1_funct_1('#skF_5',B_8) != k1_funct_1('#skF_5',A_53)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_53),k1_relat_1('#skF_5'))
      | ~ r2_hidden(B_8,k1_relat_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(A_53,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_4])).

tff(c_304,plain,(
    ! [A_53,B_8] :
      ( k1_funct_1('#skF_6',A_53) = B_8
      | k1_funct_1('#skF_5',B_8) != k1_funct_1('#skF_5',A_53)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_53),'#skF_4')
      | ~ r2_hidden(B_8,'#skF_4')
      | ~ r2_hidden(A_53,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_34,c_40,c_40,c_292])).

tff(c_329,plain,(
    ! [A_56] :
      ( k1_funct_1('#skF_6',A_56) = A_56
      | ~ r2_hidden(k1_funct_1('#skF_6',A_56),'#skF_4')
      | ~ r2_hidden(A_56,'#skF_4')
      | ~ r2_hidden(A_56,'#skF_4') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_304])).

tff(c_371,plain,(
    ! [A_59] :
      ( k1_funct_1('#skF_6',A_59) = A_59
      | ~ r2_hidden(A_59,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_211,c_329])).

tff(c_380,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_4','#skF_6')) = '#skF_3'('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_122,c_371])).

tff(c_386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_380])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:06:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.34  
% 2.42/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.35  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4
% 2.42/1.35  
% 2.42/1.35  %Foreground sorts:
% 2.42/1.35  
% 2.42/1.35  
% 2.42/1.35  %Background operators:
% 2.42/1.35  
% 2.42/1.35  
% 2.42/1.35  %Foreground operators:
% 2.42/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.42/1.35  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.42/1.35  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.42/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.42/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.42/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.42/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.42/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.42/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.42/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.42/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.42/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.42/1.35  
% 2.62/1.36  tff(f_104, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_1)).
% 2.62/1.36  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.62/1.36  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.62/1.36  tff(f_82, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, k6_relat_1(B)))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_1)).
% 2.62/1.36  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 2.62/1.36  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 2.62/1.36  tff(c_30, plain, (k6_relat_1('#skF_4')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.62/1.36  tff(c_44, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.62/1.36  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.62/1.36  tff(c_38, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.62/1.36  tff(c_221, plain, (![B_43]: (k1_funct_1(B_43, '#skF_3'(k1_relat_1(B_43), B_43))!='#skF_3'(k1_relat_1(B_43), B_43) | k6_relat_1(k1_relat_1(B_43))=B_43 | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.62/1.36  tff(c_224, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))!='#skF_3'(k1_relat_1('#skF_6'), '#skF_6') | k6_relat_1(k1_relat_1('#skF_6'))='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_38, c_221])).
% 2.62/1.36  tff(c_229, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))!='#skF_3'('#skF_4', '#skF_6') | k6_relat_1('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_38, c_224])).
% 2.62/1.36  tff(c_230, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))!='#skF_3'('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_30, c_229])).
% 2.62/1.36  tff(c_107, plain, (![B_32]: (r2_hidden('#skF_3'(k1_relat_1(B_32), B_32), k1_relat_1(B_32)) | k6_relat_1(k1_relat_1(B_32))=B_32 | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.62/1.36  tff(c_110, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_6'), k1_relat_1('#skF_6')) | k6_relat_1(k1_relat_1('#skF_6'))='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_38, c_107])).
% 2.62/1.36  tff(c_121, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_6'), '#skF_4') | k6_relat_1('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_38, c_110])).
% 2.62/1.36  tff(c_122, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_121])).
% 2.62/1.36  tff(c_36, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.62/1.36  tff(c_86, plain, (![B_27, A_28]: (k5_relat_1(B_27, k6_relat_1(A_28))=B_27 | ~r1_tarski(k2_relat_1(B_27), A_28) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.36  tff(c_89, plain, (k5_relat_1('#skF_6', k6_relat_1('#skF_4'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_86])).
% 2.62/1.36  tff(c_92, plain, (k5_relat_1('#skF_6', k6_relat_1('#skF_4'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_89])).
% 2.62/1.36  tff(c_193, plain, (![C_39, A_40, B_41]: (r2_hidden(k1_funct_1(C_39, A_40), B_41) | ~r2_hidden(A_40, k1_relat_1(k5_relat_1(C_39, k6_relat_1(B_41)))) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.62/1.36  tff(c_200, plain, (![A_40]: (r2_hidden(k1_funct_1('#skF_6', A_40), '#skF_4') | ~r2_hidden(A_40, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_193])).
% 2.62/1.36  tff(c_211, plain, (![A_40]: (r2_hidden(k1_funct_1('#skF_6', A_40), '#skF_4') | ~r2_hidden(A_40, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_200])).
% 2.62/1.36  tff(c_48, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.62/1.36  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.62/1.36  tff(c_34, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.62/1.36  tff(c_40, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.62/1.36  tff(c_32, plain, (k5_relat_1('#skF_6', '#skF_5')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.62/1.36  tff(c_257, plain, (![C_50, B_51, A_52]: (k1_funct_1(k5_relat_1(C_50, B_51), A_52)=k1_funct_1(B_51, k1_funct_1(C_50, A_52)) | ~r2_hidden(A_52, k1_relat_1(k5_relat_1(C_50, B_51))) | ~v1_funct_1(C_50) | ~v1_relat_1(C_50) | ~v1_funct_1(B_51) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.62/1.36  tff(c_278, plain, (![A_52]: (k1_funct_1(k5_relat_1('#skF_6', '#skF_5'), A_52)=k1_funct_1('#skF_5', k1_funct_1('#skF_6', A_52)) | ~r2_hidden(A_52, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_257])).
% 2.62/1.36  tff(c_287, plain, (![A_53]: (k1_funct_1('#skF_5', k1_funct_1('#skF_6', A_53))=k1_funct_1('#skF_5', A_53) | ~r2_hidden(A_53, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_32, c_278])).
% 2.62/1.36  tff(c_4, plain, (![C_9, B_8, A_3]: (C_9=B_8 | k1_funct_1(A_3, C_9)!=k1_funct_1(A_3, B_8) | ~r2_hidden(C_9, k1_relat_1(A_3)) | ~r2_hidden(B_8, k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.62/1.36  tff(c_292, plain, (![A_53, B_8]: (k1_funct_1('#skF_6', A_53)=B_8 | k1_funct_1('#skF_5', B_8)!=k1_funct_1('#skF_5', A_53) | ~r2_hidden(k1_funct_1('#skF_6', A_53), k1_relat_1('#skF_5')) | ~r2_hidden(B_8, k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(A_53, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_287, c_4])).
% 2.62/1.36  tff(c_304, plain, (![A_53, B_8]: (k1_funct_1('#skF_6', A_53)=B_8 | k1_funct_1('#skF_5', B_8)!=k1_funct_1('#skF_5', A_53) | ~r2_hidden(k1_funct_1('#skF_6', A_53), '#skF_4') | ~r2_hidden(B_8, '#skF_4') | ~r2_hidden(A_53, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_34, c_40, c_40, c_292])).
% 2.62/1.36  tff(c_329, plain, (![A_56]: (k1_funct_1('#skF_6', A_56)=A_56 | ~r2_hidden(k1_funct_1('#skF_6', A_56), '#skF_4') | ~r2_hidden(A_56, '#skF_4') | ~r2_hidden(A_56, '#skF_4'))), inference(reflexivity, [status(thm), theory('equality')], [c_304])).
% 2.62/1.36  tff(c_371, plain, (![A_59]: (k1_funct_1('#skF_6', A_59)=A_59 | ~r2_hidden(A_59, '#skF_4'))), inference(resolution, [status(thm)], [c_211, c_329])).
% 2.62/1.36  tff(c_380, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))='#skF_3'('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_122, c_371])).
% 2.62/1.36  tff(c_386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_230, c_380])).
% 2.62/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.36  
% 2.62/1.36  Inference rules
% 2.62/1.36  ----------------------
% 2.62/1.36  #Ref     : 2
% 2.62/1.36  #Sup     : 69
% 2.62/1.36  #Fact    : 0
% 2.62/1.36  #Define  : 0
% 2.62/1.36  #Split   : 3
% 2.62/1.36  #Chain   : 0
% 2.62/1.36  #Close   : 0
% 2.62/1.36  
% 2.62/1.36  Ordering : KBO
% 2.62/1.36  
% 2.62/1.36  Simplification rules
% 2.62/1.36  ----------------------
% 2.62/1.36  #Subsume      : 1
% 2.62/1.36  #Demod        : 109
% 2.62/1.36  #Tautology    : 33
% 2.62/1.36  #SimpNegUnit  : 7
% 2.62/1.36  #BackRed      : 3
% 2.62/1.36  
% 2.62/1.36  #Partial instantiations: 0
% 2.62/1.36  #Strategies tried      : 1
% 2.62/1.36  
% 2.62/1.36  Timing (in seconds)
% 2.62/1.36  ----------------------
% 2.62/1.37  Preprocessing        : 0.32
% 2.62/1.37  Parsing              : 0.17
% 2.62/1.37  CNF conversion       : 0.02
% 2.62/1.37  Main loop            : 0.27
% 2.62/1.37  Inferencing          : 0.10
% 2.62/1.37  Reduction            : 0.09
% 2.62/1.37  Demodulation         : 0.06
% 2.62/1.37  BG Simplification    : 0.02
% 2.62/1.37  Subsumption          : 0.04
% 2.62/1.37  Abstraction          : 0.02
% 2.62/1.37  MUC search           : 0.00
% 2.62/1.37  Cooper               : 0.00
% 2.62/1.37  Total                : 0.62
% 2.62/1.37  Index Insertion      : 0.00
% 2.62/1.37  Index Deletion       : 0.00
% 2.62/1.37  Index Matching       : 0.00
% 2.62/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
