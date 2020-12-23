%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:41 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 113 expanded)
%              Number of leaves         :   27 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  137 ( 453 expanded)
%              Number of equality atoms :   42 ( 171 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(f_108,negated_conjecture,(
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

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,k6_relat_1(B))))
      <=> ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
           => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(f_50,axiom,(
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

tff(c_32,plain,(
    k6_relat_1('#skF_4') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_46,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_40,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_289,plain,(
    ! [B_55] :
      ( k1_funct_1(B_55,'#skF_3'(k1_relat_1(B_55),B_55)) != '#skF_3'(k1_relat_1(B_55),B_55)
      | k6_relat_1(k1_relat_1(B_55)) = B_55
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_292,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4','#skF_6')) != '#skF_3'(k1_relat_1('#skF_6'),'#skF_6')
    | k6_relat_1(k1_relat_1('#skF_6')) = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_289])).

tff(c_297,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4','#skF_6')) != '#skF_3'('#skF_4','#skF_6')
    | k6_relat_1('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_40,c_292])).

tff(c_298,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_4','#skF_6')) != '#skF_3'('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_297])).

tff(c_118,plain,(
    ! [B_36] :
      ( r2_hidden('#skF_3'(k1_relat_1(B_36),B_36),k1_relat_1(B_36))
      | k6_relat_1(k1_relat_1(B_36)) = B_36
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_121,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_6'),k1_relat_1('#skF_6'))
    | k6_relat_1(k1_relat_1('#skF_6')) = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_118])).

tff(c_132,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_6'),'#skF_4')
    | k6_relat_1('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_40,c_121])).

tff(c_133,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_132])).

tff(c_38,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_72,plain,(
    ! [A_27,B_28] :
      ( k8_relat_1(A_27,B_28) = B_28
      | ~ r1_tarski(k2_relat_1(B_28),A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_75,plain,
    ( k8_relat_1('#skF_4','#skF_6') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_72])).

tff(c_78,plain,(
    k8_relat_1('#skF_4','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_75])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = k8_relat_1(A_1,B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_221,plain,(
    ! [C_45,A_46,B_47] :
      ( r2_hidden(k1_funct_1(C_45,A_46),B_47)
      | ~ r2_hidden(A_46,k1_relat_1(k5_relat_1(C_45,k6_relat_1(B_47))))
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_261,plain,(
    ! [B_51,A_52,A_53] :
      ( r2_hidden(k1_funct_1(B_51,A_52),A_53)
      | ~ r2_hidden(A_52,k1_relat_1(k8_relat_1(A_53,B_51)))
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_221])).

tff(c_276,plain,(
    ! [A_52] :
      ( r2_hidden(k1_funct_1('#skF_6',A_52),'#skF_4')
      | ~ r2_hidden(A_52,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_261])).

tff(c_281,plain,(
    ! [A_52] :
      ( r2_hidden(k1_funct_1('#skF_6',A_52),'#skF_4')
      | ~ r2_hidden(A_52,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_44,c_40,c_276])).

tff(c_50,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34,plain,(
    k5_relat_1('#skF_6','#skF_5') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_337,plain,(
    ! [C_65,B_66,A_67] :
      ( k1_funct_1(k5_relat_1(C_65,B_66),A_67) = k1_funct_1(B_66,k1_funct_1(C_65,A_67))
      | ~ r2_hidden(A_67,k1_relat_1(k5_relat_1(C_65,B_66)))
      | ~ v1_funct_1(C_65)
      | ~ v1_relat_1(C_65)
      | ~ v1_funct_1(B_66)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_358,plain,(
    ! [A_67] :
      ( k1_funct_1(k5_relat_1('#skF_6','#skF_5'),A_67) = k1_funct_1('#skF_5',k1_funct_1('#skF_6',A_67))
      | ~ r2_hidden(A_67,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_337])).

tff(c_365,plain,(
    ! [A_68] :
      ( k1_funct_1('#skF_5',k1_funct_1('#skF_6',A_68)) = k1_funct_1('#skF_5',A_68)
      | ~ r2_hidden(A_68,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_34,c_358])).

tff(c_6,plain,(
    ! [C_11,B_10,A_5] :
      ( C_11 = B_10
      | k1_funct_1(A_5,C_11) != k1_funct_1(A_5,B_10)
      | ~ r2_hidden(C_11,k1_relat_1(A_5))
      | ~ r2_hidden(B_10,k1_relat_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_370,plain,(
    ! [A_68,B_10] :
      ( k1_funct_1('#skF_6',A_68) = B_10
      | k1_funct_1('#skF_5',B_10) != k1_funct_1('#skF_5',A_68)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_68),k1_relat_1('#skF_5'))
      | ~ r2_hidden(B_10,k1_relat_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(A_68,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_6])).

tff(c_382,plain,(
    ! [A_68,B_10] :
      ( k1_funct_1('#skF_6',A_68) = B_10
      | k1_funct_1('#skF_5',B_10) != k1_funct_1('#skF_5',A_68)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_68),'#skF_4')
      | ~ r2_hidden(B_10,'#skF_4')
      | ~ r2_hidden(A_68,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_36,c_42,c_42,c_370])).

tff(c_406,plain,(
    ! [A_71] :
      ( k1_funct_1('#skF_6',A_71) = A_71
      | ~ r2_hidden(k1_funct_1('#skF_6',A_71),'#skF_4')
      | ~ r2_hidden(A_71,'#skF_4')
      | ~ r2_hidden(A_71,'#skF_4') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_382])).

tff(c_436,plain,(
    ! [A_74] :
      ( k1_funct_1('#skF_6',A_74) = A_74
      | ~ r2_hidden(A_74,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_281,c_406])).

tff(c_445,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_4','#skF_6')) = '#skF_3'('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_133,c_436])).

tff(c_451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_298,c_445])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:26:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.30  
% 2.29/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.30  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4
% 2.29/1.30  
% 2.29/1.30  %Foreground sorts:
% 2.29/1.30  
% 2.29/1.30  
% 2.29/1.30  %Background operators:
% 2.29/1.30  
% 2.29/1.30  
% 2.29/1.30  %Foreground operators:
% 2.29/1.30  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.29/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.29/1.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.29/1.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.29/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.29/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.29/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.29/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.29/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.29/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.29/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.30  
% 2.29/1.31  tff(f_108, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_1)).
% 2.29/1.31  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.29/1.31  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.29/1.31  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.29/1.31  tff(f_86, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, k6_relat_1(B)))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_1)).
% 2.29/1.31  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) => (k1_funct_1(k5_relat_1(C, B), A) = k1_funct_1(B, k1_funct_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 2.29/1.31  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 2.29/1.31  tff(c_32, plain, (k6_relat_1('#skF_4')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.29/1.31  tff(c_46, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.29/1.31  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.29/1.31  tff(c_40, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.29/1.31  tff(c_289, plain, (![B_55]: (k1_funct_1(B_55, '#skF_3'(k1_relat_1(B_55), B_55))!='#skF_3'(k1_relat_1(B_55), B_55) | k6_relat_1(k1_relat_1(B_55))=B_55 | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.29/1.31  tff(c_292, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))!='#skF_3'(k1_relat_1('#skF_6'), '#skF_6') | k6_relat_1(k1_relat_1('#skF_6'))='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_40, c_289])).
% 2.29/1.31  tff(c_297, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))!='#skF_3'('#skF_4', '#skF_6') | k6_relat_1('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_40, c_292])).
% 2.29/1.31  tff(c_298, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))!='#skF_3'('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_32, c_297])).
% 2.29/1.31  tff(c_118, plain, (![B_36]: (r2_hidden('#skF_3'(k1_relat_1(B_36), B_36), k1_relat_1(B_36)) | k6_relat_1(k1_relat_1(B_36))=B_36 | ~v1_funct_1(B_36) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.29/1.31  tff(c_121, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_6'), k1_relat_1('#skF_6')) | k6_relat_1(k1_relat_1('#skF_6'))='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_40, c_118])).
% 2.29/1.31  tff(c_132, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_6'), '#skF_4') | k6_relat_1('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_40, c_121])).
% 2.29/1.31  tff(c_133, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_32, c_132])).
% 2.29/1.31  tff(c_38, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.29/1.31  tff(c_72, plain, (![A_27, B_28]: (k8_relat_1(A_27, B_28)=B_28 | ~r1_tarski(k2_relat_1(B_28), A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.29/1.31  tff(c_75, plain, (k8_relat_1('#skF_4', '#skF_6')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_72])).
% 2.29/1.31  tff(c_78, plain, (k8_relat_1('#skF_4', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_75])).
% 2.29/1.31  tff(c_2, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=k8_relat_1(A_1, B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.31  tff(c_221, plain, (![C_45, A_46, B_47]: (r2_hidden(k1_funct_1(C_45, A_46), B_47) | ~r2_hidden(A_46, k1_relat_1(k5_relat_1(C_45, k6_relat_1(B_47)))) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.29/1.31  tff(c_261, plain, (![B_51, A_52, A_53]: (r2_hidden(k1_funct_1(B_51, A_52), A_53) | ~r2_hidden(A_52, k1_relat_1(k8_relat_1(A_53, B_51))) | ~v1_funct_1(B_51) | ~v1_relat_1(B_51) | ~v1_relat_1(B_51))), inference(superposition, [status(thm), theory('equality')], [c_2, c_221])).
% 2.29/1.31  tff(c_276, plain, (![A_52]: (r2_hidden(k1_funct_1('#skF_6', A_52), '#skF_4') | ~r2_hidden(A_52, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_261])).
% 2.29/1.31  tff(c_281, plain, (![A_52]: (r2_hidden(k1_funct_1('#skF_6', A_52), '#skF_4') | ~r2_hidden(A_52, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_44, c_40, c_276])).
% 2.29/1.31  tff(c_50, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.29/1.31  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.29/1.31  tff(c_36, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.29/1.31  tff(c_42, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.29/1.31  tff(c_34, plain, (k5_relat_1('#skF_6', '#skF_5')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.29/1.31  tff(c_337, plain, (![C_65, B_66, A_67]: (k1_funct_1(k5_relat_1(C_65, B_66), A_67)=k1_funct_1(B_66, k1_funct_1(C_65, A_67)) | ~r2_hidden(A_67, k1_relat_1(k5_relat_1(C_65, B_66))) | ~v1_funct_1(C_65) | ~v1_relat_1(C_65) | ~v1_funct_1(B_66) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.29/1.31  tff(c_358, plain, (![A_67]: (k1_funct_1(k5_relat_1('#skF_6', '#skF_5'), A_67)=k1_funct_1('#skF_5', k1_funct_1('#skF_6', A_67)) | ~r2_hidden(A_67, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_337])).
% 2.29/1.31  tff(c_365, plain, (![A_68]: (k1_funct_1('#skF_5', k1_funct_1('#skF_6', A_68))=k1_funct_1('#skF_5', A_68) | ~r2_hidden(A_68, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_34, c_358])).
% 2.29/1.31  tff(c_6, plain, (![C_11, B_10, A_5]: (C_11=B_10 | k1_funct_1(A_5, C_11)!=k1_funct_1(A_5, B_10) | ~r2_hidden(C_11, k1_relat_1(A_5)) | ~r2_hidden(B_10, k1_relat_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.29/1.31  tff(c_370, plain, (![A_68, B_10]: (k1_funct_1('#skF_6', A_68)=B_10 | k1_funct_1('#skF_5', B_10)!=k1_funct_1('#skF_5', A_68) | ~r2_hidden(k1_funct_1('#skF_6', A_68), k1_relat_1('#skF_5')) | ~r2_hidden(B_10, k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(A_68, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_365, c_6])).
% 2.29/1.31  tff(c_382, plain, (![A_68, B_10]: (k1_funct_1('#skF_6', A_68)=B_10 | k1_funct_1('#skF_5', B_10)!=k1_funct_1('#skF_5', A_68) | ~r2_hidden(k1_funct_1('#skF_6', A_68), '#skF_4') | ~r2_hidden(B_10, '#skF_4') | ~r2_hidden(A_68, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_36, c_42, c_42, c_370])).
% 2.29/1.31  tff(c_406, plain, (![A_71]: (k1_funct_1('#skF_6', A_71)=A_71 | ~r2_hidden(k1_funct_1('#skF_6', A_71), '#skF_4') | ~r2_hidden(A_71, '#skF_4') | ~r2_hidden(A_71, '#skF_4'))), inference(reflexivity, [status(thm), theory('equality')], [c_382])).
% 2.29/1.31  tff(c_436, plain, (![A_74]: (k1_funct_1('#skF_6', A_74)=A_74 | ~r2_hidden(A_74, '#skF_4'))), inference(resolution, [status(thm)], [c_281, c_406])).
% 2.29/1.31  tff(c_445, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))='#skF_3'('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_133, c_436])).
% 2.29/1.31  tff(c_451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_298, c_445])).
% 2.29/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.31  
% 2.29/1.31  Inference rules
% 2.29/1.31  ----------------------
% 2.29/1.31  #Ref     : 3
% 2.29/1.31  #Sup     : 85
% 2.29/1.31  #Fact    : 0
% 2.29/1.31  #Define  : 0
% 2.29/1.31  #Split   : 2
% 2.29/1.31  #Chain   : 0
% 2.29/1.31  #Close   : 0
% 2.29/1.31  
% 2.29/1.31  Ordering : KBO
% 2.29/1.31  
% 2.29/1.31  Simplification rules
% 2.29/1.31  ----------------------
% 2.29/1.31  #Subsume      : 1
% 2.29/1.31  #Demod        : 102
% 2.29/1.31  #Tautology    : 40
% 2.29/1.31  #SimpNegUnit  : 7
% 2.29/1.31  #BackRed      : 1
% 2.29/1.31  
% 2.29/1.31  #Partial instantiations: 0
% 2.29/1.31  #Strategies tried      : 1
% 2.29/1.31  
% 2.29/1.31  Timing (in seconds)
% 2.29/1.31  ----------------------
% 2.29/1.31  Preprocessing        : 0.32
% 2.29/1.31  Parsing              : 0.17
% 2.29/1.31  CNF conversion       : 0.02
% 2.29/1.31  Main loop            : 0.27
% 2.29/1.31  Inferencing          : 0.10
% 2.29/1.31  Reduction            : 0.08
% 2.29/1.31  Demodulation         : 0.06
% 2.29/1.32  BG Simplification    : 0.02
% 2.29/1.32  Subsumption          : 0.04
% 2.29/1.32  Abstraction          : 0.02
% 2.29/1.32  MUC search           : 0.00
% 2.29/1.32  Cooper               : 0.00
% 2.29/1.32  Total                : 0.62
% 2.29/1.32  Index Insertion      : 0.00
% 2.29/1.32  Index Deletion       : 0.00
% 2.29/1.32  Index Matching       : 0.00
% 2.29/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
