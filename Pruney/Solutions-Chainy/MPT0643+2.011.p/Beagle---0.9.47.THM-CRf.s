%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:41 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 109 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  139 ( 456 expanded)
%              Number of equality atoms :   38 ( 168 expanded)
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

tff(f_103,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_40,axiom,(
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

tff(c_28,plain,(
    k6_relat_1('#skF_4') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_519,plain,(
    ! [B_65] :
      ( k1_funct_1(B_65,'#skF_3'(k1_relat_1(B_65),B_65)) != '#skF_3'(k1_relat_1(B_65),B_65)
      | k6_relat_1(k1_relat_1(B_65)) = B_65
      | ~ v1_funct_1(B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_522,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4','#skF_6')) != '#skF_3'(k1_relat_1('#skF_6'),'#skF_6')
    | k6_relat_1(k1_relat_1('#skF_6')) = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_519])).

tff(c_527,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4','#skF_6')) != '#skF_3'('#skF_4','#skF_6')
    | k6_relat_1('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_36,c_522])).

tff(c_528,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_4','#skF_6')) != '#skF_3'('#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_527])).

tff(c_94,plain,(
    ! [B_29] :
      ( r2_hidden('#skF_3'(k1_relat_1(B_29),B_29),k1_relat_1(B_29))
      | k6_relat_1(k1_relat_1(B_29)) = B_29
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_97,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_6'),k1_relat_1('#skF_6'))
    | k6_relat_1(k1_relat_1('#skF_6')) = '#skF_6'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_94])).

tff(c_108,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_6'),'#skF_4')
    | k6_relat_1('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_36,c_97])).

tff(c_109,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_108])).

tff(c_38,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_30,plain,(
    k5_relat_1('#skF_6','#skF_5') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_554,plain,(
    ! [C_69,A_70,B_71] :
      ( r2_hidden(k1_funct_1(C_69,A_70),k1_relat_1(B_71))
      | ~ r2_hidden(A_70,k1_relat_1(k5_relat_1(C_69,B_71)))
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69)
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_567,plain,(
    ! [C_69,A_70] :
      ( r2_hidden(k1_funct_1(C_69,A_70),'#skF_4')
      | ~ r2_hidden(A_70,k1_relat_1(k5_relat_1(C_69,'#skF_5')))
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_554])).

tff(c_594,plain,(
    ! [C_74,A_75] :
      ( r2_hidden(k1_funct_1(C_74,A_75),'#skF_4')
      | ~ r2_hidden(A_75,k1_relat_1(k5_relat_1(C_74,'#skF_5')))
      | ~ v1_funct_1(C_74)
      | ~ v1_relat_1(C_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_567])).

tff(c_613,plain,(
    ! [A_75] :
      ( r2_hidden(k1_funct_1('#skF_6',A_75),'#skF_4')
      | ~ r2_hidden(A_75,k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_594])).

tff(c_619,plain,(
    ! [A_75] :
      ( r2_hidden(k1_funct_1('#skF_6',A_75),'#skF_4')
      | ~ r2_hidden(A_75,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_613])).

tff(c_32,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_627,plain,(
    ! [B_77,C_78,A_79] :
      ( k1_funct_1(k5_relat_1(B_77,C_78),A_79) = k1_funct_1(C_78,k1_funct_1(B_77,A_79))
      | ~ r2_hidden(A_79,k1_relat_1(B_77))
      | ~ v1_funct_1(C_78)
      | ~ v1_relat_1(C_78)
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_637,plain,(
    ! [C_78,A_79] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_78),A_79) = k1_funct_1(C_78,k1_funct_1('#skF_6',A_79))
      | ~ r2_hidden(A_79,'#skF_4')
      | ~ v1_funct_1(C_78)
      | ~ v1_relat_1(C_78)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_627])).

tff(c_657,plain,(
    ! [C_83,A_84] :
      ( k1_funct_1(k5_relat_1('#skF_6',C_83),A_84) = k1_funct_1(C_83,k1_funct_1('#skF_6',A_84))
      | ~ r2_hidden(A_84,'#skF_4')
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_637])).

tff(c_685,plain,(
    ! [A_84] :
      ( k1_funct_1('#skF_5',k1_funct_1('#skF_6',A_84)) = k1_funct_1('#skF_5',A_84)
      | ~ r2_hidden(A_84,'#skF_4')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_657])).

tff(c_690,plain,(
    ! [A_85] :
      ( k1_funct_1('#skF_5',k1_funct_1('#skF_6',A_85)) = k1_funct_1('#skF_5',A_85)
      | ~ r2_hidden(A_85,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_685])).

tff(c_2,plain,(
    ! [C_7,B_6,A_1] :
      ( C_7 = B_6
      | k1_funct_1(A_1,C_7) != k1_funct_1(A_1,B_6)
      | ~ r2_hidden(C_7,k1_relat_1(A_1))
      | ~ r2_hidden(B_6,k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_695,plain,(
    ! [A_85,B_6] :
      ( k1_funct_1('#skF_6',A_85) = B_6
      | k1_funct_1('#skF_5',B_6) != k1_funct_1('#skF_5',A_85)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_85),k1_relat_1('#skF_5'))
      | ~ r2_hidden(B_6,k1_relat_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(A_85,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_2])).

tff(c_710,plain,(
    ! [A_85,B_6] :
      ( k1_funct_1('#skF_6',A_85) = B_6
      | k1_funct_1('#skF_5',B_6) != k1_funct_1('#skF_5',A_85)
      | ~ r2_hidden(k1_funct_1('#skF_6',A_85),'#skF_4')
      | ~ r2_hidden(B_6,'#skF_4')
      | ~ r2_hidden(A_85,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_32,c_38,c_38,c_695])).

tff(c_778,plain,(
    ! [A_91] :
      ( k1_funct_1('#skF_6',A_91) = A_91
      | ~ r2_hidden(k1_funct_1('#skF_6',A_91),'#skF_4')
      | ~ r2_hidden(A_91,'#skF_4')
      | ~ r2_hidden(A_91,'#skF_4') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_710])).

tff(c_796,plain,(
    ! [A_92] :
      ( k1_funct_1('#skF_6',A_92) = A_92
      | ~ r2_hidden(A_92,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_619,c_778])).

tff(c_808,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_4','#skF_6')) = '#skF_3'('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_109,c_796])).

tff(c_815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_528,c_808])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n025.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:52:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.45  
% 3.04/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.45  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4
% 3.04/1.45  
% 3.04/1.45  %Foreground sorts:
% 3.04/1.45  
% 3.04/1.45  
% 3.04/1.45  %Background operators:
% 3.04/1.45  
% 3.04/1.45  
% 3.04/1.45  %Foreground operators:
% 3.04/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.04/1.45  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.04/1.45  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.04/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.04/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.04/1.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.04/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.04/1.45  tff('#skF_5', type, '#skF_5': $i).
% 3.04/1.45  tff('#skF_6', type, '#skF_6': $i).
% 3.04/1.45  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.04/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.04/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.04/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.04/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.04/1.45  
% 3.04/1.46  tff(f_103, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_1)).
% 3.04/1.46  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 3.04/1.46  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 3.04/1.46  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 3.04/1.46  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 3.04/1.46  tff(c_28, plain, (k6_relat_1('#skF_4')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.04/1.46  tff(c_42, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.04/1.46  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.04/1.46  tff(c_36, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.04/1.46  tff(c_519, plain, (![B_65]: (k1_funct_1(B_65, '#skF_3'(k1_relat_1(B_65), B_65))!='#skF_3'(k1_relat_1(B_65), B_65) | k6_relat_1(k1_relat_1(B_65))=B_65 | ~v1_funct_1(B_65) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.04/1.46  tff(c_522, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))!='#skF_3'(k1_relat_1('#skF_6'), '#skF_6') | k6_relat_1(k1_relat_1('#skF_6'))='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_36, c_519])).
% 3.04/1.46  tff(c_527, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))!='#skF_3'('#skF_4', '#skF_6') | k6_relat_1('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_36, c_522])).
% 3.04/1.46  tff(c_528, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))!='#skF_3'('#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_28, c_527])).
% 3.04/1.46  tff(c_94, plain, (![B_29]: (r2_hidden('#skF_3'(k1_relat_1(B_29), B_29), k1_relat_1(B_29)) | k6_relat_1(k1_relat_1(B_29))=B_29 | ~v1_funct_1(B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.04/1.46  tff(c_97, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_6'), k1_relat_1('#skF_6')) | k6_relat_1(k1_relat_1('#skF_6'))='#skF_6' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_36, c_94])).
% 3.04/1.46  tff(c_108, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_6'), '#skF_4') | k6_relat_1('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_36, c_97])).
% 3.04/1.46  tff(c_109, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_28, c_108])).
% 3.04/1.46  tff(c_38, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.04/1.46  tff(c_30, plain, (k5_relat_1('#skF_6', '#skF_5')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.04/1.46  tff(c_46, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.04/1.46  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.04/1.46  tff(c_554, plain, (![C_69, A_70, B_71]: (r2_hidden(k1_funct_1(C_69, A_70), k1_relat_1(B_71)) | ~r2_hidden(A_70, k1_relat_1(k5_relat_1(C_69, B_71))) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69) | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.04/1.47  tff(c_567, plain, (![C_69, A_70]: (r2_hidden(k1_funct_1(C_69, A_70), '#skF_4') | ~r2_hidden(A_70, k1_relat_1(k5_relat_1(C_69, '#skF_5'))) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_554])).
% 3.04/1.47  tff(c_594, plain, (![C_74, A_75]: (r2_hidden(k1_funct_1(C_74, A_75), '#skF_4') | ~r2_hidden(A_75, k1_relat_1(k5_relat_1(C_74, '#skF_5'))) | ~v1_funct_1(C_74) | ~v1_relat_1(C_74))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_567])).
% 3.04/1.47  tff(c_613, plain, (![A_75]: (r2_hidden(k1_funct_1('#skF_6', A_75), '#skF_4') | ~r2_hidden(A_75, k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_594])).
% 3.04/1.47  tff(c_619, plain, (![A_75]: (r2_hidden(k1_funct_1('#skF_6', A_75), '#skF_4') | ~r2_hidden(A_75, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_613])).
% 3.04/1.47  tff(c_32, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.04/1.47  tff(c_627, plain, (![B_77, C_78, A_79]: (k1_funct_1(k5_relat_1(B_77, C_78), A_79)=k1_funct_1(C_78, k1_funct_1(B_77, A_79)) | ~r2_hidden(A_79, k1_relat_1(B_77)) | ~v1_funct_1(C_78) | ~v1_relat_1(C_78) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.04/1.47  tff(c_637, plain, (![C_78, A_79]: (k1_funct_1(k5_relat_1('#skF_6', C_78), A_79)=k1_funct_1(C_78, k1_funct_1('#skF_6', A_79)) | ~r2_hidden(A_79, '#skF_4') | ~v1_funct_1(C_78) | ~v1_relat_1(C_78) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_627])).
% 3.04/1.47  tff(c_657, plain, (![C_83, A_84]: (k1_funct_1(k5_relat_1('#skF_6', C_83), A_84)=k1_funct_1(C_83, k1_funct_1('#skF_6', A_84)) | ~r2_hidden(A_84, '#skF_4') | ~v1_funct_1(C_83) | ~v1_relat_1(C_83))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_637])).
% 3.04/1.47  tff(c_685, plain, (![A_84]: (k1_funct_1('#skF_5', k1_funct_1('#skF_6', A_84))=k1_funct_1('#skF_5', A_84) | ~r2_hidden(A_84, '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_657])).
% 3.04/1.47  tff(c_690, plain, (![A_85]: (k1_funct_1('#skF_5', k1_funct_1('#skF_6', A_85))=k1_funct_1('#skF_5', A_85) | ~r2_hidden(A_85, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_685])).
% 3.04/1.47  tff(c_2, plain, (![C_7, B_6, A_1]: (C_7=B_6 | k1_funct_1(A_1, C_7)!=k1_funct_1(A_1, B_6) | ~r2_hidden(C_7, k1_relat_1(A_1)) | ~r2_hidden(B_6, k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.04/1.47  tff(c_695, plain, (![A_85, B_6]: (k1_funct_1('#skF_6', A_85)=B_6 | k1_funct_1('#skF_5', B_6)!=k1_funct_1('#skF_5', A_85) | ~r2_hidden(k1_funct_1('#skF_6', A_85), k1_relat_1('#skF_5')) | ~r2_hidden(B_6, k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(A_85, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_690, c_2])).
% 3.04/1.47  tff(c_710, plain, (![A_85, B_6]: (k1_funct_1('#skF_6', A_85)=B_6 | k1_funct_1('#skF_5', B_6)!=k1_funct_1('#skF_5', A_85) | ~r2_hidden(k1_funct_1('#skF_6', A_85), '#skF_4') | ~r2_hidden(B_6, '#skF_4') | ~r2_hidden(A_85, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_32, c_38, c_38, c_695])).
% 3.04/1.47  tff(c_778, plain, (![A_91]: (k1_funct_1('#skF_6', A_91)=A_91 | ~r2_hidden(k1_funct_1('#skF_6', A_91), '#skF_4') | ~r2_hidden(A_91, '#skF_4') | ~r2_hidden(A_91, '#skF_4'))), inference(reflexivity, [status(thm), theory('equality')], [c_710])).
% 3.04/1.47  tff(c_796, plain, (![A_92]: (k1_funct_1('#skF_6', A_92)=A_92 | ~r2_hidden(A_92, '#skF_4'))), inference(resolution, [status(thm)], [c_619, c_778])).
% 3.04/1.47  tff(c_808, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', '#skF_6'))='#skF_3'('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_109, c_796])).
% 3.04/1.47  tff(c_815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_528, c_808])).
% 3.04/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.47  
% 3.04/1.47  Inference rules
% 3.04/1.47  ----------------------
% 3.04/1.47  #Ref     : 3
% 3.04/1.47  #Sup     : 169
% 3.04/1.47  #Fact    : 0
% 3.04/1.47  #Define  : 0
% 3.04/1.47  #Split   : 3
% 3.04/1.47  #Chain   : 0
% 3.04/1.47  #Close   : 0
% 3.04/1.47  
% 3.04/1.47  Ordering : KBO
% 3.04/1.47  
% 3.04/1.47  Simplification rules
% 3.04/1.47  ----------------------
% 3.04/1.47  #Subsume      : 4
% 3.04/1.47  #Demod        : 221
% 3.04/1.47  #Tautology    : 59
% 3.04/1.47  #SimpNegUnit  : 8
% 3.04/1.47  #BackRed      : 1
% 3.04/1.47  
% 3.04/1.47  #Partial instantiations: 0
% 3.04/1.47  #Strategies tried      : 1
% 3.04/1.47  
% 3.04/1.47  Timing (in seconds)
% 3.04/1.47  ----------------------
% 3.04/1.47  Preprocessing        : 0.31
% 3.04/1.47  Parsing              : 0.16
% 3.04/1.47  CNF conversion       : 0.02
% 3.04/1.47  Main loop            : 0.38
% 3.04/1.47  Inferencing          : 0.14
% 3.04/1.47  Reduction            : 0.12
% 3.04/1.47  Demodulation         : 0.08
% 3.04/1.47  BG Simplification    : 0.03
% 3.04/1.47  Subsumption          : 0.07
% 3.04/1.47  Abstraction          : 0.02
% 3.04/1.47  MUC search           : 0.00
% 3.04/1.47  Cooper               : 0.00
% 3.04/1.47  Total                : 0.72
% 3.04/1.47  Index Insertion      : 0.00
% 3.04/1.47  Index Deletion       : 0.00
% 3.04/1.47  Index Matching       : 0.00
% 3.04/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
