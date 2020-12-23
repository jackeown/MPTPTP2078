%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:34 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   58 (  96 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   96 ( 173 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( k2_xboole_0(A_24,B_25) = B_25
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_26])).

tff(c_486,plain,(
    ! [A_76,B_77] :
      ( k2_xboole_0(k2_relat_1(A_76),k2_relat_1(B_77)) = k2_relat_1(k2_xboole_0(A_76,B_77))
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1256,plain,(
    ! [A_103,B_104] :
      ( r1_tarski(k2_relat_1(A_103),k2_relat_1(k2_xboole_0(A_103,B_104)))
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_8])).

tff(c_1295,plain,
    ( r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1256])).

tff(c_1303,plain,(
    r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_1295])).

tff(c_112,plain,(
    ! [A_39] :
      ( k2_xboole_0(k1_relat_1(A_39),k2_relat_1(A_39)) = k3_relat_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_124,plain,(
    ! [A_1,A_39] :
      ( r1_tarski(A_1,k3_relat_1(A_39))
      | ~ r1_tarski(A_1,k2_relat_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_2])).

tff(c_133,plain,(
    ! [A_40] :
      ( r1_tarski(k1_relat_1(A_40),k3_relat_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_8])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_140,plain,(
    ! [A_40] :
      ( k2_xboole_0(k1_relat_1(A_40),k3_relat_1(A_40)) = k3_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(resolution,[status(thm)],[c_133,c_4])).

tff(c_265,plain,(
    ! [A_54,B_55] :
      ( k2_xboole_0(k1_relat_1(A_54),k1_relat_1(B_55)) = k1_relat_1(k2_xboole_0(A_54,B_55))
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_816,plain,(
    ! [A_95,B_96] :
      ( r1_tarski(k1_relat_1(A_95),k1_relat_1(k2_xboole_0(A_95,B_96)))
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(A_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_8])).

tff(c_846,plain,
    ( r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_816])).

tff(c_854,plain,(
    r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_846])).

tff(c_867,plain,(
    k2_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_854,c_4])).

tff(c_33,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k2_xboole_0(A_9,B_10) ),
    inference(resolution,[status(thm)],[c_8,c_26])).

tff(c_79,plain,(
    ! [A_31,C_32,B_33] :
      ( r1_tarski(A_31,C_32)
      | ~ r1_tarski(B_33,C_32)
      | ~ r1_tarski(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_307,plain,(
    ! [A_59,C_60,B_61,A_62] :
      ( r1_tarski(A_59,k2_xboole_0(C_60,B_61))
      | ~ r1_tarski(A_59,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(resolution,[status(thm)],[c_2,c_79])).

tff(c_366,plain,(
    ! [A_65,C_66,B_67,B_68] :
      ( r1_tarski(A_65,k2_xboole_0(C_66,B_67))
      | ~ r1_tarski(k2_xboole_0(A_65,B_68),B_67) ) ),
    inference(resolution,[status(thm)],[c_8,c_307])).

tff(c_404,plain,(
    ! [A_69,C_70,B_71,B_72] : r1_tarski(A_69,k2_xboole_0(C_70,k2_xboole_0(k2_xboole_0(A_69,B_71),B_72))) ),
    inference(resolution,[status(thm)],[c_8,c_366])).

tff(c_436,plain,(
    ! [A_69,B_71,B_10] : r1_tarski(A_69,k2_xboole_0(k2_xboole_0(A_69,B_71),B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_404])).

tff(c_925,plain,(
    ! [B_97] : r1_tarski(k1_relat_1('#skF_1'),k2_xboole_0(k1_relat_1('#skF_2'),B_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_867,c_436])).

tff(c_942,plain,
    ( r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_925])).

tff(c_958,plain,(
    r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_942])).

tff(c_12,plain,(
    ! [A_14] :
      ( k2_xboole_0(k1_relat_1(A_14),k2_relat_1(A_14)) = k3_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_141,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(k2_xboole_0(A_41,C_42),B_43)
      | ~ r1_tarski(C_42,B_43)
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1637,plain,(
    ! [A_113,B_114] :
      ( r1_tarski(k3_relat_1(A_113),B_114)
      | ~ r1_tarski(k2_relat_1(A_113),B_114)
      | ~ r1_tarski(k1_relat_1(A_113),B_114)
      | ~ v1_relat_1(A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_141])).

tff(c_18,plain,(
    ~ r1_tarski(k3_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1669,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k3_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1637,c_18])).

tff(c_1690,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k3_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_958,c_1669])).

tff(c_1707,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_124,c_1690])).

tff(c_1715,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1303,c_1707])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:43:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.57  
% 3.54/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.57  %$ r1_tarski > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.54/1.57  
% 3.54/1.57  %Foreground sorts:
% 3.54/1.57  
% 3.54/1.57  
% 3.54/1.57  %Background operators:
% 3.54/1.57  
% 3.54/1.57  
% 3.54/1.57  %Foreground operators:
% 3.54/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.57  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.54/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.54/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.54/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.54/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.54/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.54/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.54/1.57  
% 3.54/1.58  tff(f_75, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 3.54/1.58  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.54/1.58  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_relat_1)).
% 3.54/1.58  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.54/1.58  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.54/1.58  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.54/1.58  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relat_1)).
% 3.54/1.58  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.54/1.58  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.54/1.58  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.54/1.58  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.54/1.58  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.54/1.58  tff(c_26, plain, (![A_24, B_25]: (k2_xboole_0(A_24, B_25)=B_25 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.54/1.58  tff(c_34, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_20, c_26])).
% 3.54/1.58  tff(c_486, plain, (![A_76, B_77]: (k2_xboole_0(k2_relat_1(A_76), k2_relat_1(B_77))=k2_relat_1(k2_xboole_0(A_76, B_77)) | ~v1_relat_1(B_77) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.54/1.58  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.54/1.58  tff(c_1256, plain, (![A_103, B_104]: (r1_tarski(k2_relat_1(A_103), k2_relat_1(k2_xboole_0(A_103, B_104))) | ~v1_relat_1(B_104) | ~v1_relat_1(A_103))), inference(superposition, [status(thm), theory('equality')], [c_486, c_8])).
% 3.54/1.58  tff(c_1295, plain, (r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34, c_1256])).
% 3.54/1.58  tff(c_1303, plain, (r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_1295])).
% 3.54/1.58  tff(c_112, plain, (![A_39]: (k2_xboole_0(k1_relat_1(A_39), k2_relat_1(A_39))=k3_relat_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.54/1.58  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.54/1.58  tff(c_124, plain, (![A_1, A_39]: (r1_tarski(A_1, k3_relat_1(A_39)) | ~r1_tarski(A_1, k2_relat_1(A_39)) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_112, c_2])).
% 3.54/1.58  tff(c_133, plain, (![A_40]: (r1_tarski(k1_relat_1(A_40), k3_relat_1(A_40)) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_112, c_8])).
% 3.54/1.58  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.54/1.58  tff(c_140, plain, (![A_40]: (k2_xboole_0(k1_relat_1(A_40), k3_relat_1(A_40))=k3_relat_1(A_40) | ~v1_relat_1(A_40))), inference(resolution, [status(thm)], [c_133, c_4])).
% 3.54/1.58  tff(c_265, plain, (![A_54, B_55]: (k2_xboole_0(k1_relat_1(A_54), k1_relat_1(B_55))=k1_relat_1(k2_xboole_0(A_54, B_55)) | ~v1_relat_1(B_55) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.54/1.58  tff(c_816, plain, (![A_95, B_96]: (r1_tarski(k1_relat_1(A_95), k1_relat_1(k2_xboole_0(A_95, B_96))) | ~v1_relat_1(B_96) | ~v1_relat_1(A_95))), inference(superposition, [status(thm), theory('equality')], [c_265, c_8])).
% 3.54/1.58  tff(c_846, plain, (r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34, c_816])).
% 3.54/1.58  tff(c_854, plain, (r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_846])).
% 3.54/1.58  tff(c_867, plain, (k2_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_854, c_4])).
% 3.54/1.58  tff(c_33, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k2_xboole_0(A_9, B_10))), inference(resolution, [status(thm)], [c_8, c_26])).
% 3.54/1.58  tff(c_79, plain, (![A_31, C_32, B_33]: (r1_tarski(A_31, C_32) | ~r1_tarski(B_33, C_32) | ~r1_tarski(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.58  tff(c_307, plain, (![A_59, C_60, B_61, A_62]: (r1_tarski(A_59, k2_xboole_0(C_60, B_61)) | ~r1_tarski(A_59, A_62) | ~r1_tarski(A_62, B_61))), inference(resolution, [status(thm)], [c_2, c_79])).
% 3.54/1.58  tff(c_366, plain, (![A_65, C_66, B_67, B_68]: (r1_tarski(A_65, k2_xboole_0(C_66, B_67)) | ~r1_tarski(k2_xboole_0(A_65, B_68), B_67))), inference(resolution, [status(thm)], [c_8, c_307])).
% 3.54/1.58  tff(c_404, plain, (![A_69, C_70, B_71, B_72]: (r1_tarski(A_69, k2_xboole_0(C_70, k2_xboole_0(k2_xboole_0(A_69, B_71), B_72))))), inference(resolution, [status(thm)], [c_8, c_366])).
% 3.54/1.58  tff(c_436, plain, (![A_69, B_71, B_10]: (r1_tarski(A_69, k2_xboole_0(k2_xboole_0(A_69, B_71), B_10)))), inference(superposition, [status(thm), theory('equality')], [c_33, c_404])).
% 3.54/1.58  tff(c_925, plain, (![B_97]: (r1_tarski(k1_relat_1('#skF_1'), k2_xboole_0(k1_relat_1('#skF_2'), B_97)))), inference(superposition, [status(thm), theory('equality')], [c_867, c_436])).
% 3.54/1.58  tff(c_942, plain, (r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_140, c_925])).
% 3.54/1.58  tff(c_958, plain, (r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_942])).
% 3.54/1.58  tff(c_12, plain, (![A_14]: (k2_xboole_0(k1_relat_1(A_14), k2_relat_1(A_14))=k3_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.54/1.58  tff(c_141, plain, (![A_41, C_42, B_43]: (r1_tarski(k2_xboole_0(A_41, C_42), B_43) | ~r1_tarski(C_42, B_43) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.54/1.58  tff(c_1637, plain, (![A_113, B_114]: (r1_tarski(k3_relat_1(A_113), B_114) | ~r1_tarski(k2_relat_1(A_113), B_114) | ~r1_tarski(k1_relat_1(A_113), B_114) | ~v1_relat_1(A_113))), inference(superposition, [status(thm), theory('equality')], [c_12, c_141])).
% 3.54/1.58  tff(c_18, plain, (~r1_tarski(k3_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.54/1.58  tff(c_1669, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_1'), k3_relat_1('#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1637, c_18])).
% 3.54/1.58  tff(c_1690, plain, (~r1_tarski(k2_relat_1('#skF_1'), k3_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_958, c_1669])).
% 3.54/1.58  tff(c_1707, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_124, c_1690])).
% 3.54/1.58  tff(c_1715, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_1303, c_1707])).
% 3.54/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.58  
% 3.54/1.58  Inference rules
% 3.54/1.58  ----------------------
% 3.54/1.58  #Ref     : 0
% 3.54/1.58  #Sup     : 461
% 3.54/1.58  #Fact    : 0
% 3.54/1.58  #Define  : 0
% 3.54/1.58  #Split   : 4
% 3.54/1.58  #Chain   : 0
% 3.54/1.58  #Close   : 0
% 3.54/1.58  
% 3.54/1.58  Ordering : KBO
% 3.54/1.58  
% 3.54/1.58  Simplification rules
% 3.54/1.58  ----------------------
% 3.54/1.58  #Subsume      : 77
% 3.54/1.58  #Demod        : 116
% 3.54/1.58  #Tautology    : 113
% 3.54/1.58  #SimpNegUnit  : 0
% 3.54/1.58  #BackRed      : 0
% 3.54/1.58  
% 3.54/1.58  #Partial instantiations: 0
% 3.54/1.58  #Strategies tried      : 1
% 3.54/1.58  
% 3.54/1.58  Timing (in seconds)
% 3.54/1.58  ----------------------
% 3.54/1.58  Preprocessing        : 0.27
% 3.54/1.58  Parsing              : 0.15
% 3.54/1.58  CNF conversion       : 0.02
% 3.54/1.58  Main loop            : 0.56
% 3.54/1.58  Inferencing          : 0.19
% 3.54/1.58  Reduction            : 0.17
% 3.54/1.58  Demodulation         : 0.13
% 3.54/1.58  BG Simplification    : 0.02
% 3.54/1.58  Subsumption          : 0.13
% 3.54/1.59  Abstraction          : 0.03
% 3.54/1.59  MUC search           : 0.00
% 3.54/1.59  Cooper               : 0.00
% 3.54/1.59  Total                : 0.86
% 3.54/1.59  Index Insertion      : 0.00
% 3.54/1.59  Index Deletion       : 0.00
% 3.54/1.59  Index Matching       : 0.00
% 3.54/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
