%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:41 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 107 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  135 ( 429 expanded)
%              Number of equality atoms :   42 ( 162 expanded)
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
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

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

tff(c_248,plain,(
    ! [B_47,C_48,A_49] :
      ( k1_funct_1(k5_relat_1(B_47,C_48),A_49) = k1_funct_1(C_48,k1_funct_1(B_47,A_49))
      | ~ r2_hidden(A_49,k1_relat_1(B_47))
      | ~ v1_funct_1(C_48)
      | ~ v1_relat_1(C_48)
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_258,plain,(
    ! [C_48,A_49] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_48),A_49) = k1_funct_1(C_48,k1_funct_1('#skF_6',A_49))
      | ~ r2_hidden(A_49,'#skF_4')
      | ~ v1_funct_1(C_48)
      | ~ v1_relat_1(C_48)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_248])).

tff(c_269,plain,(
    ! [C_50,A_51] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_50),A_51) = k1_funct_1(C_50,k1_funct_1('#skF_6',A_51))
      | ~ r2_hidden(A_51,'#skF_4')
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_258])).

tff(c_293,plain,(
    ! [A_51] :
      ( k1_funct_1('#skF_5',k1_funct_1('#skF_6',A_51)) = k1_funct_1('#skF_5',A_51)
      | ~ r2_hidden(A_51,'#skF_4')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_269])).

tff(c_297,plain,(
    ! [A_51] :
      ( k1_funct_1('#skF_5',k1_funct_1('#skF_6',A_51)) = k1_funct_1('#skF_5',A_51)
      | ~ r2_hidden(A_51,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_293])).

tff(c_339,plain,(
    ! [C_55,B_56,A_57] :
      ( C_55 = B_56
      | k1_funct_1(A_57,C_55) != k1_funct_1(A_57,B_56)
      | ~ r2_hidden(C_55,k1_relat_1(A_57))
      | ~ r2_hidden(B_56,k1_relat_1(A_57))
      | ~ v2_funct_1(A_57)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_345,plain,(
    ! [A_51,B_56] :
      ( k1_funct_1('#skF_6',A_51) = B_56
      | k1_funct_1('#skF_5',B_56) != k1_funct_1('#skF_5',A_51)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_51),k1_relat_1('#skF_5'))
      | ~ r2_hidden(B_56,k1_relat_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(A_51,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_339])).

tff(c_357,plain,(
    ! [A_51,B_56] :
      ( k1_funct_1('#skF_6',A_51) = B_56
      | k1_funct_1('#skF_5',B_56) != k1_funct_1('#skF_5',A_51)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_51),'#skF_4')
      | ~ r2_hidden(B_56,'#skF_4')
      | ~ r2_hidden(A_51,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_34,c_40,c_40,c_345])).

tff(c_429,plain,(
    ! [A_62] :
      ( k1_funct_1('#skF_6',A_62) = A_62
      | ~ r2_hidden(k1_funct_1('#skF_6',A_62),'#skF_4')
      | ~ r2_hidden(A_62,'#skF_4')
      | ~ r2_hidden(A_62,'#skF_4') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_357])).

tff(c_440,plain,(
    ! [A_63] :
      ( k1_funct_1('#skF_6',A_63) = A_63
      | ~ r2_hidden(A_63,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_211,c_429])).

tff(c_449,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_4','#skF_6')) = '#skF_3'('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_122,c_440])).

tff(c_455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:18:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.37  
% 2.67/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.37  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4
% 2.67/1.37  
% 2.67/1.37  %Foreground sorts:
% 2.67/1.37  
% 2.67/1.37  
% 2.67/1.37  %Background operators:
% 2.67/1.37  
% 2.67/1.37  
% 2.67/1.37  %Foreground operators:
% 2.67/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.67/1.37  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.67/1.37  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.67/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.67/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.67/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.67/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.67/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.67/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.67/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.67/1.37  
% 2.67/1.39  tff(f_104, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_1)).
% 2.67/1.39  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.67/1.39  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.67/1.39  tff(f_82, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, k6_relat_1(B)))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_1)).
% 2.67/1.39  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 2.67/1.39  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 2.67/1.39  tff(c_30, plain, (k6_relat_1('#skF_4')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.67/1.39  tff(c_44, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.67/1.39  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.67/1.39  tff(c_38, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.67/1.39  tff(c_221, plain, (![B_43]: (k1_funct_1(B_43, '#skF_3'(k1_relat_1(B_43), B_43))!='#skF_3'(k1_relat_1(B_43), B_43) | k6_relat_1(k1_relat_1(B_43))=B_43 | ~v1_funct_1(B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.67/1.39  tff(c_224, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))!='#skF_3'(k1_relat_1('#skF_6'), '#skF_6') | k6_relat_1(k1_relat_1('#skF_6'))='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_38, c_221])).
% 2.67/1.39  tff(c_229, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))!='#skF_3'('#skF_4', '#skF_6') | k6_relat_1('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_38, c_224])).
% 2.67/1.39  tff(c_230, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))!='#skF_3'('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_30, c_229])).
% 2.67/1.39  tff(c_107, plain, (![B_32]: (r2_hidden('#skF_3'(k1_relat_1(B_32), B_32), k1_relat_1(B_32)) | k6_relat_1(k1_relat_1(B_32))=B_32 | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.67/1.39  tff(c_110, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_6'), k1_relat_1('#skF_6')) | k6_relat_1(k1_relat_1('#skF_6'))='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_38, c_107])).
% 2.67/1.39  tff(c_121, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_6'), '#skF_4') | k6_relat_1('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_38, c_110])).
% 2.67/1.39  tff(c_122, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_121])).
% 2.67/1.39  tff(c_36, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.67/1.39  tff(c_86, plain, (![B_27, A_28]: (k5_relat_1(B_27, k6_relat_1(A_28))=B_27 | ~r1_tarski(k2_relat_1(B_27), A_28) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.39  tff(c_89, plain, (k5_relat_1('#skF_6', k6_relat_1('#skF_4'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_86])).
% 2.67/1.39  tff(c_92, plain, (k5_relat_1('#skF_6', k6_relat_1('#skF_4'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_89])).
% 2.67/1.39  tff(c_193, plain, (![C_39, A_40, B_41]: (r2_hidden(k1_funct_1(C_39, A_40), B_41) | ~r2_hidden(A_40, k1_relat_1(k5_relat_1(C_39, k6_relat_1(B_41)))) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.67/1.39  tff(c_200, plain, (![A_40]: (r2_hidden(k1_funct_1('#skF_6', A_40), '#skF_4') | ~r2_hidden(A_40, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_193])).
% 2.67/1.39  tff(c_211, plain, (![A_40]: (r2_hidden(k1_funct_1('#skF_6', A_40), '#skF_4') | ~r2_hidden(A_40, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_200])).
% 2.67/1.39  tff(c_48, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.67/1.39  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.67/1.39  tff(c_34, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.67/1.39  tff(c_40, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.67/1.39  tff(c_32, plain, (k5_relat_1('#skF_6', '#skF_5')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.67/1.39  tff(c_248, plain, (![B_47, C_48, A_49]: (k1_funct_1(k5_relat_1(B_47, C_48), A_49)=k1_funct_1(C_48, k1_funct_1(B_47, A_49)) | ~r2_hidden(A_49, k1_relat_1(B_47)) | ~v1_funct_1(C_48) | ~v1_relat_1(C_48) | ~v1_funct_1(B_47) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.39  tff(c_258, plain, (![C_48, A_49]: (k1_funct_1(k5_relat_1('#skF_6', C_48), A_49)=k1_funct_1(C_48, k1_funct_1('#skF_6', A_49)) | ~r2_hidden(A_49, '#skF_4') | ~v1_funct_1(C_48) | ~v1_relat_1(C_48) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_248])).
% 2.67/1.39  tff(c_269, plain, (![C_50, A_51]: (k1_funct_1(k5_relat_1('#skF_6', C_50), A_51)=k1_funct_1(C_50, k1_funct_1('#skF_6', A_51)) | ~r2_hidden(A_51, '#skF_4') | ~v1_funct_1(C_50) | ~v1_relat_1(C_50))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_258])).
% 2.67/1.39  tff(c_293, plain, (![A_51]: (k1_funct_1('#skF_5', k1_funct_1('#skF_6', A_51))=k1_funct_1('#skF_5', A_51) | ~r2_hidden(A_51, '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_269])).
% 2.67/1.39  tff(c_297, plain, (![A_51]: (k1_funct_1('#skF_5', k1_funct_1('#skF_6', A_51))=k1_funct_1('#skF_5', A_51) | ~r2_hidden(A_51, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_293])).
% 2.67/1.39  tff(c_339, plain, (![C_55, B_56, A_57]: (C_55=B_56 | k1_funct_1(A_57, C_55)!=k1_funct_1(A_57, B_56) | ~r2_hidden(C_55, k1_relat_1(A_57)) | ~r2_hidden(B_56, k1_relat_1(A_57)) | ~v2_funct_1(A_57) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.67/1.39  tff(c_345, plain, (![A_51, B_56]: (k1_funct_1('#skF_6', A_51)=B_56 | k1_funct_1('#skF_5', B_56)!=k1_funct_1('#skF_5', A_51) | ~r2_hidden(k1_funct_1('#skF_6', A_51), k1_relat_1('#skF_5')) | ~r2_hidden(B_56, k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(A_51, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_297, c_339])).
% 2.67/1.39  tff(c_357, plain, (![A_51, B_56]: (k1_funct_1('#skF_6', A_51)=B_56 | k1_funct_1('#skF_5', B_56)!=k1_funct_1('#skF_5', A_51) | ~r2_hidden(k1_funct_1('#skF_6', A_51), '#skF_4') | ~r2_hidden(B_56, '#skF_4') | ~r2_hidden(A_51, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_34, c_40, c_40, c_345])).
% 2.67/1.39  tff(c_429, plain, (![A_62]: (k1_funct_1('#skF_6', A_62)=A_62 | ~r2_hidden(k1_funct_1('#skF_6', A_62), '#skF_4') | ~r2_hidden(A_62, '#skF_4') | ~r2_hidden(A_62, '#skF_4'))), inference(reflexivity, [status(thm), theory('equality')], [c_357])).
% 2.67/1.39  tff(c_440, plain, (![A_63]: (k1_funct_1('#skF_6', A_63)=A_63 | ~r2_hidden(A_63, '#skF_4'))), inference(resolution, [status(thm)], [c_211, c_429])).
% 2.67/1.39  tff(c_449, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))='#skF_3'('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_122, c_440])).
% 2.67/1.39  tff(c_455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_230, c_449])).
% 2.67/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.39  
% 2.67/1.39  Inference rules
% 2.67/1.39  ----------------------
% 2.67/1.39  #Ref     : 2
% 2.67/1.39  #Sup     : 89
% 2.67/1.39  #Fact    : 0
% 2.67/1.39  #Define  : 0
% 2.67/1.39  #Split   : 3
% 2.67/1.39  #Chain   : 0
% 2.67/1.39  #Close   : 0
% 2.67/1.39  
% 2.67/1.39  Ordering : KBO
% 2.67/1.39  
% 2.67/1.39  Simplification rules
% 2.67/1.39  ----------------------
% 2.67/1.39  #Subsume      : 2
% 2.67/1.39  #Demod        : 112
% 2.67/1.39  #Tautology    : 43
% 2.67/1.39  #SimpNegUnit  : 7
% 2.67/1.39  #BackRed      : 3
% 2.67/1.39  
% 2.67/1.39  #Partial instantiations: 0
% 2.67/1.39  #Strategies tried      : 1
% 2.67/1.39  
% 2.67/1.39  Timing (in seconds)
% 2.67/1.39  ----------------------
% 2.67/1.39  Preprocessing        : 0.32
% 2.67/1.39  Parsing              : 0.16
% 2.67/1.39  CNF conversion       : 0.02
% 2.67/1.39  Main loop            : 0.30
% 2.67/1.39  Inferencing          : 0.11
% 2.67/1.39  Reduction            : 0.10
% 2.67/1.39  Demodulation         : 0.07
% 2.67/1.39  BG Simplification    : 0.02
% 2.67/1.39  Subsumption          : 0.05
% 2.67/1.39  Abstraction          : 0.02
% 2.67/1.39  MUC search           : 0.00
% 2.67/1.39  Cooper               : 0.00
% 2.67/1.39  Total                : 0.66
% 2.67/1.39  Index Insertion      : 0.00
% 2.67/1.39  Index Deletion       : 0.00
% 2.67/1.39  Index Matching       : 0.00
% 2.67/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
