%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:42 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   54 (  93 expanded)
%              Number of leaves         :   22 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :  121 ( 282 expanded)
%              Number of equality atoms :   43 ( 112 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_98,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( r1_tarski(k2_relat_1(B),k1_relat_1(A))
                    & r1_tarski(k2_relat_1(C),k1_relat_1(A))
                    & k1_relat_1(B) = k1_relat_1(C)
                    & k5_relat_1(B,A) = k5_relat_1(C,A) )
                 => B = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_1)).

tff(c_34,plain,(
    k6_relat_1('#skF_3') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_8,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_3] : v1_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    ! [A_23] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_23)),A_23) = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_94,plain,(
    ! [A_1] :
      ( k5_relat_1(k6_relat_1(A_1),k6_relat_1(A_1)) = k6_relat_1(A_1)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_85])).

tff(c_104,plain,(
    ! [A_1] : k5_relat_1(k6_relat_1(A_1),k6_relat_1(A_1)) = k6_relat_1(A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_94])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_203,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(k2_relat_1(B_37),k1_relat_1(A_38))
      | k1_relat_1(k5_relat_1(B_37,A_38)) != k1_relat_1(B_37)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_212,plain,(
    ! [A_1,A_38] :
      ( r1_tarski(A_1,k1_relat_1(A_38))
      | k1_relat_1(k5_relat_1(k6_relat_1(A_1),A_38)) != k1_relat_1(k6_relat_1(A_1))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_203])).

tff(c_227,plain,(
    ! [A_39,A_40] :
      ( r1_tarski(A_39,k1_relat_1(A_40))
      | k1_relat_1(k5_relat_1(k6_relat_1(A_39),A_40)) != A_39
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10,c_2,c_212])).

tff(c_233,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,k1_relat_1(k6_relat_1(A_1)))
      | k1_relat_1(k6_relat_1(A_1)) != A_1
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_227])).

tff(c_244,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10,c_2,c_2,c_233])).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_44,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_100,plain,
    ( k5_relat_1(k6_relat_1('#skF_3'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_85])).

tff(c_108,plain,(
    k5_relat_1(k6_relat_1('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_100])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_38,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_48,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_42,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    k5_relat_1('#skF_5','#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_255,plain,(
    ! [C_41,B_42,A_43] :
      ( C_41 = B_42
      | k5_relat_1(C_41,A_43) != k5_relat_1(B_42,A_43)
      | k1_relat_1(C_41) != k1_relat_1(B_42)
      | ~ r1_tarski(k2_relat_1(C_41),k1_relat_1(A_43))
      | ~ r1_tarski(k2_relat_1(B_42),k1_relat_1(A_43))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42)
      | ~ v2_funct_1(A_43)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_281,plain,(
    ! [B_42] :
      ( B_42 = '#skF_5'
      | k5_relat_1(B_42,'#skF_4') != '#skF_4'
      | k1_relat_1(B_42) != k1_relat_1('#skF_5')
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(B_42),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42)
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_255])).

tff(c_369,plain,(
    ! [B_51] :
      ( B_51 = '#skF_5'
      | k5_relat_1(B_51,'#skF_4') != '#skF_4'
      | k1_relat_1(B_51) != '#skF_3'
      | ~ r1_tarski(k2_relat_1(B_51),'#skF_3')
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_38,c_48,c_46,c_44,c_40,c_44,c_42,c_281])).

tff(c_389,plain,(
    ! [A_1] :
      ( k6_relat_1(A_1) = '#skF_5'
      | k5_relat_1(k6_relat_1(A_1),'#skF_4') != '#skF_4'
      | k1_relat_1(k6_relat_1(A_1)) != '#skF_3'
      | ~ r1_tarski(A_1,'#skF_3')
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_369])).

tff(c_401,plain,(
    ! [A_52] :
      ( k6_relat_1(A_52) = '#skF_5'
      | k5_relat_1(k6_relat_1(A_52),'#skF_4') != '#skF_4'
      | A_52 != '#skF_3'
      | ~ r1_tarski(A_52,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10,c_2,c_389])).

tff(c_404,plain,
    ( k6_relat_1('#skF_3') = '#skF_5'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_401])).

tff(c_411,plain,(
    k6_relat_1('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_404])).

tff(c_413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_411])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.35  
% 2.42/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/1.35  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
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
% 2.42/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.42/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.42/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.42/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.42/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.42/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.42/1.35  
% 2.68/1.36  tff(f_98, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_1)).
% 2.68/1.36  tff(f_37, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.68/1.36  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.68/1.36  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 2.68/1.36  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 2.68/1.36  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((r1_tarski(k2_relat_1(B), k1_relat_1(A)) & r1_tarski(k2_relat_1(C), k1_relat_1(A))) & (k1_relat_1(B) = k1_relat_1(C))) & (k5_relat_1(B, A) = k5_relat_1(C, A))) => (B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_funct_1)).
% 2.68/1.36  tff(c_34, plain, (k6_relat_1('#skF_3')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.36  tff(c_8, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.68/1.36  tff(c_10, plain, (![A_3]: (v1_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.68/1.36  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.36  tff(c_85, plain, (![A_23]: (k5_relat_1(k6_relat_1(k1_relat_1(A_23)), A_23)=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.68/1.36  tff(c_94, plain, (![A_1]: (k5_relat_1(k6_relat_1(A_1), k6_relat_1(A_1))=k6_relat_1(A_1) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_85])).
% 2.68/1.36  tff(c_104, plain, (![A_1]: (k5_relat_1(k6_relat_1(A_1), k6_relat_1(A_1))=k6_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_94])).
% 2.68/1.36  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.36  tff(c_203, plain, (![B_37, A_38]: (r1_tarski(k2_relat_1(B_37), k1_relat_1(A_38)) | k1_relat_1(k5_relat_1(B_37, A_38))!=k1_relat_1(B_37) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.68/1.36  tff(c_212, plain, (![A_1, A_38]: (r1_tarski(A_1, k1_relat_1(A_38)) | k1_relat_1(k5_relat_1(k6_relat_1(A_1), A_38))!=k1_relat_1(k6_relat_1(A_1)) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_4, c_203])).
% 2.68/1.36  tff(c_227, plain, (![A_39, A_40]: (r1_tarski(A_39, k1_relat_1(A_40)) | k1_relat_1(k5_relat_1(k6_relat_1(A_39), A_40))!=A_39 | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_2, c_212])).
% 2.68/1.36  tff(c_233, plain, (![A_1]: (r1_tarski(A_1, k1_relat_1(k6_relat_1(A_1))) | k1_relat_1(k6_relat_1(A_1))!=A_1 | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_227])).
% 2.68/1.36  tff(c_244, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_2, c_2, c_233])).
% 2.68/1.36  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.36  tff(c_44, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.36  tff(c_100, plain, (k5_relat_1(k6_relat_1('#skF_3'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_44, c_85])).
% 2.68/1.36  tff(c_108, plain, (k5_relat_1(k6_relat_1('#skF_3'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_100])).
% 2.68/1.36  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.36  tff(c_38, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.36  tff(c_48, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.36  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.36  tff(c_40, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.36  tff(c_42, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.36  tff(c_36, plain, (k5_relat_1('#skF_5', '#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.68/1.36  tff(c_255, plain, (![C_41, B_42, A_43]: (C_41=B_42 | k5_relat_1(C_41, A_43)!=k5_relat_1(B_42, A_43) | k1_relat_1(C_41)!=k1_relat_1(B_42) | ~r1_tarski(k2_relat_1(C_41), k1_relat_1(A_43)) | ~r1_tarski(k2_relat_1(B_42), k1_relat_1(A_43)) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42) | ~v2_funct_1(A_43) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.68/1.36  tff(c_281, plain, (![B_42]: (B_42='#skF_5' | k5_relat_1(B_42, '#skF_4')!='#skF_4' | k1_relat_1(B_42)!=k1_relat_1('#skF_5') | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1(B_42), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1(B_42) | ~v1_relat_1(B_42) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_255])).
% 2.68/1.36  tff(c_369, plain, (![B_51]: (B_51='#skF_5' | k5_relat_1(B_51, '#skF_4')!='#skF_4' | k1_relat_1(B_51)!='#skF_3' | ~r1_tarski(k2_relat_1(B_51), '#skF_3') | ~v1_funct_1(B_51) | ~v1_relat_1(B_51))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_38, c_48, c_46, c_44, c_40, c_44, c_42, c_281])).
% 2.68/1.36  tff(c_389, plain, (![A_1]: (k6_relat_1(A_1)='#skF_5' | k5_relat_1(k6_relat_1(A_1), '#skF_4')!='#skF_4' | k1_relat_1(k6_relat_1(A_1))!='#skF_3' | ~r1_tarski(A_1, '#skF_3') | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_369])).
% 2.68/1.36  tff(c_401, plain, (![A_52]: (k6_relat_1(A_52)='#skF_5' | k5_relat_1(k6_relat_1(A_52), '#skF_4')!='#skF_4' | A_52!='#skF_3' | ~r1_tarski(A_52, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_2, c_389])).
% 2.68/1.36  tff(c_404, plain, (k6_relat_1('#skF_3')='#skF_5' | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_108, c_401])).
% 2.68/1.36  tff(c_411, plain, (k6_relat_1('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_244, c_404])).
% 2.68/1.36  tff(c_413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_411])).
% 2.68/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.36  
% 2.68/1.36  Inference rules
% 2.68/1.36  ----------------------
% 2.68/1.36  #Ref     : 1
% 2.68/1.36  #Sup     : 77
% 2.68/1.36  #Fact    : 0
% 2.68/1.36  #Define  : 0
% 2.68/1.36  #Split   : 1
% 2.68/1.36  #Chain   : 0
% 2.68/1.36  #Close   : 0
% 2.68/1.36  
% 2.68/1.36  Ordering : KBO
% 2.68/1.36  
% 2.68/1.36  Simplification rules
% 2.68/1.36  ----------------------
% 2.68/1.36  #Subsume      : 1
% 2.68/1.36  #Demod        : 165
% 2.68/1.36  #Tautology    : 40
% 2.68/1.36  #SimpNegUnit  : 1
% 2.68/1.36  #BackRed      : 0
% 2.68/1.36  
% 2.68/1.36  #Partial instantiations: 0
% 2.68/1.36  #Strategies tried      : 1
% 2.68/1.36  
% 2.68/1.36  Timing (in seconds)
% 2.68/1.36  ----------------------
% 2.68/1.37  Preprocessing        : 0.31
% 2.68/1.37  Parsing              : 0.16
% 2.68/1.37  CNF conversion       : 0.02
% 2.68/1.37  Main loop            : 0.28
% 2.68/1.37  Inferencing          : 0.11
% 2.68/1.37  Reduction            : 0.09
% 2.68/1.37  Demodulation         : 0.07
% 2.68/1.37  BG Simplification    : 0.02
% 2.68/1.37  Subsumption          : 0.05
% 2.68/1.37  Abstraction          : 0.02
% 2.68/1.37  MUC search           : 0.00
% 2.68/1.37  Cooper               : 0.00
% 2.68/1.37  Total                : 0.62
% 2.68/1.37  Index Insertion      : 0.00
% 2.68/1.37  Index Deletion       : 0.00
% 2.68/1.37  Index Matching       : 0.00
% 2.68/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
