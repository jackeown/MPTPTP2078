%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:02 EST 2020

% Result     : Theorem 8.05s
% Output     : CNFRefutation 8.05s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 155 expanded)
%              Number of leaves         :   25 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  123 ( 464 expanded)
%              Number of equality atoms :   41 ( 163 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k4_xboole_0 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & k2_relat_1(A) = k1_relat_1(B)
                & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_56,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_32,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_34,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_18,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_57,plain,(
    v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_18])).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_44,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_38,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_160,plain,(
    ! [A_36] :
      ( k4_relat_1(A_36) = k2_funct_1(A_36)
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_166,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_160])).

tff(c_170,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_166])).

tff(c_92,plain,(
    ! [A_27] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_27)),A_27) = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_101,plain,
    ( k5_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_92])).

tff(c_105,plain,(
    k5_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_101])).

tff(c_61,plain,(
    ! [A_25] : k4_relat_1(k6_relat_1(A_25)) = k6_relat_1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_70,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_61])).

tff(c_73,plain,(
    k4_relat_1(k5_relat_1('#skF_1','#skF_2')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_70])).

tff(c_259,plain,(
    ! [B_40,A_41] :
      ( k5_relat_1(k4_relat_1(B_40),k4_relat_1(A_41)) = k4_relat_1(k5_relat_1(A_41,B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_268,plain,(
    ! [A_41] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k4_relat_1(A_41)) = k4_relat_1(k5_relat_1(A_41,'#skF_1'))
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_259])).

tff(c_298,plain,(
    ! [A_42] :
      ( k5_relat_1(k2_funct_1('#skF_1'),k4_relat_1(A_42)) = k4_relat_1(k5_relat_1(A_42,'#skF_1'))
      | ~ v1_relat_1(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_268])).

tff(c_310,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k4_relat_1(k5_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_1'))
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_298])).

tff(c_319,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_170,c_105,c_310])).

tff(c_26,plain,(
    ! [A_20] :
      ( v1_relat_1(k2_funct_1(A_20))
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12,plain,(
    ! [A_16] : k4_relat_1(k6_relat_1(A_16)) = k6_relat_1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_271,plain,(
    ! [B_40] :
      ( k5_relat_1(k4_relat_1(B_40),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1',B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_259])).

tff(c_330,plain,(
    ! [B_43] :
      ( k5_relat_1(k4_relat_1(B_43),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1',B_43))
      | ~ v1_relat_1(B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_271])).

tff(c_345,plain,(
    ! [A_16] :
      ( k5_relat_1(k6_relat_1(A_16),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1',k6_relat_1(A_16)))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_330])).

tff(c_374,plain,(
    ! [A_45] : k5_relat_1(k6_relat_1(A_45),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1',k6_relat_1(A_45))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_345])).

tff(c_14,plain,(
    ! [A_17] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_17)),A_17) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_381,plain,
    ( k4_relat_1(k5_relat_1('#skF_1',k6_relat_1(k1_relat_1(k2_funct_1('#skF_1'))))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_14])).

tff(c_2282,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_381])).

tff(c_2285,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_2282])).

tff(c_2289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_2285])).

tff(c_2291,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_36,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_28,plain,(
    ! [A_21] :
      ( k5_relat_1(k2_funct_1(A_21),A_21) = k6_relat_1(k2_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_505,plain,(
    ! [A_51,B_52,C_53] :
      ( k5_relat_1(k5_relat_1(A_51,B_52),C_53) = k5_relat_1(A_51,k5_relat_1(B_52,C_53))
      | ~ v1_relat_1(C_53)
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3313,plain,(
    ! [A_101,C_102] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_101)),C_102) = k5_relat_1(k2_funct_1(A_101),k5_relat_1(A_101,C_102))
      | ~ v1_relat_1(C_102)
      | ~ v1_relat_1(A_101)
      | ~ v1_relat_1(k2_funct_1(A_101))
      | ~ v2_funct_1(A_101)
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_505])).

tff(c_3573,plain,(
    ! [C_102] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_102) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_102))
      | ~ v1_relat_1(C_102)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_3313])).

tff(c_6268,plain,(
    ! [C_121] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_121) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_121))
      | ~ v1_relat_1(C_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_2291,c_46,c_3573])).

tff(c_6370,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6268,c_14])).

tff(c_6480,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_319,c_6370])).

tff(c_6482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.05/2.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.05/2.68  
% 8.05/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.05/2.68  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > k4_xboole_0 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 8.05/2.68  
% 8.05/2.68  %Foreground sorts:
% 8.05/2.68  
% 8.05/2.68  
% 8.05/2.68  %Background operators:
% 8.05/2.68  
% 8.05/2.68  
% 8.05/2.68  %Foreground operators:
% 8.05/2.68  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 8.05/2.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.05/2.68  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.05/2.68  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.05/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.05/2.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.05/2.68  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.05/2.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.05/2.68  tff('#skF_2', type, '#skF_2': $i).
% 8.05/2.68  tff('#skF_1', type, '#skF_1': $i).
% 8.05/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.05/2.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.05/2.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.05/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.05/2.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.05/2.68  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 8.05/2.68  
% 8.05/2.69  tff(f_112, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 8.05/2.69  tff(f_72, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 8.05/2.69  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 8.05/2.69  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 8.05/2.69  tff(f_56, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 8.05/2.69  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 8.05/2.69  tff(f_84, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 8.05/2.69  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 8.05/2.69  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 8.05/2.69  tff(c_32, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.05/2.69  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.05/2.69  tff(c_34, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.05/2.69  tff(c_18, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.05/2.69  tff(c_57, plain, (v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_18])).
% 8.05/2.69  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.05/2.69  tff(c_44, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.05/2.69  tff(c_38, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.05/2.69  tff(c_160, plain, (![A_36]: (k4_relat_1(A_36)=k2_funct_1(A_36) | ~v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.05/2.69  tff(c_166, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_38, c_160])).
% 8.05/2.69  tff(c_170, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_166])).
% 8.05/2.69  tff(c_92, plain, (![A_27]: (k5_relat_1(k6_relat_1(k1_relat_1(A_27)), A_27)=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.05/2.69  tff(c_101, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34, c_92])).
% 8.05/2.69  tff(c_105, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_101])).
% 8.05/2.69  tff(c_61, plain, (![A_25]: (k4_relat_1(k6_relat_1(A_25))=k6_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.05/2.69  tff(c_70, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_61])).
% 8.05/2.69  tff(c_73, plain, (k4_relat_1(k5_relat_1('#skF_1', '#skF_2'))=k5_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_70])).
% 8.05/2.69  tff(c_259, plain, (![B_40, A_41]: (k5_relat_1(k4_relat_1(B_40), k4_relat_1(A_41))=k4_relat_1(k5_relat_1(A_41, B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.05/2.69  tff(c_268, plain, (![A_41]: (k5_relat_1(k2_funct_1('#skF_1'), k4_relat_1(A_41))=k4_relat_1(k5_relat_1(A_41, '#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_41))), inference(superposition, [status(thm), theory('equality')], [c_170, c_259])).
% 8.05/2.69  tff(c_298, plain, (![A_42]: (k5_relat_1(k2_funct_1('#skF_1'), k4_relat_1(A_42))=k4_relat_1(k5_relat_1(A_42, '#skF_1')) | ~v1_relat_1(A_42))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_268])).
% 8.05/2.69  tff(c_310, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k4_relat_1(k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_1')) | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_298])).
% 8.05/2.69  tff(c_319, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_170, c_105, c_310])).
% 8.05/2.69  tff(c_26, plain, (![A_20]: (v1_relat_1(k2_funct_1(A_20)) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.05/2.69  tff(c_12, plain, (![A_16]: (k4_relat_1(k6_relat_1(A_16))=k6_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.05/2.69  tff(c_271, plain, (![B_40]: (k5_relat_1(k4_relat_1(B_40), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_170, c_259])).
% 8.05/2.69  tff(c_330, plain, (![B_43]: (k5_relat_1(k4_relat_1(B_43), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', B_43)) | ~v1_relat_1(B_43))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_271])).
% 8.05/2.69  tff(c_345, plain, (![A_16]: (k5_relat_1(k6_relat_1(A_16), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', k6_relat_1(A_16))) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_330])).
% 8.05/2.69  tff(c_374, plain, (![A_45]: (k5_relat_1(k6_relat_1(A_45), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', k6_relat_1(A_45))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_345])).
% 8.05/2.69  tff(c_14, plain, (![A_17]: (k5_relat_1(k6_relat_1(k1_relat_1(A_17)), A_17)=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.05/2.69  tff(c_381, plain, (k4_relat_1(k5_relat_1('#skF_1', k6_relat_1(k1_relat_1(k2_funct_1('#skF_1')))))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_374, c_14])).
% 8.05/2.69  tff(c_2282, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_381])).
% 8.05/2.69  tff(c_2285, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_2282])).
% 8.05/2.69  tff(c_2289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_2285])).
% 8.05/2.69  tff(c_2291, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_381])).
% 8.05/2.69  tff(c_36, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.05/2.69  tff(c_28, plain, (![A_21]: (k5_relat_1(k2_funct_1(A_21), A_21)=k6_relat_1(k2_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.05/2.69  tff(c_505, plain, (![A_51, B_52, C_53]: (k5_relat_1(k5_relat_1(A_51, B_52), C_53)=k5_relat_1(A_51, k5_relat_1(B_52, C_53)) | ~v1_relat_1(C_53) | ~v1_relat_1(B_52) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.05/2.69  tff(c_3313, plain, (![A_101, C_102]: (k5_relat_1(k6_relat_1(k2_relat_1(A_101)), C_102)=k5_relat_1(k2_funct_1(A_101), k5_relat_1(A_101, C_102)) | ~v1_relat_1(C_102) | ~v1_relat_1(A_101) | ~v1_relat_1(k2_funct_1(A_101)) | ~v2_funct_1(A_101) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(superposition, [status(thm), theory('equality')], [c_28, c_505])).
% 8.05/2.69  tff(c_3573, plain, (![C_102]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_102)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_102)) | ~v1_relat_1(C_102) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_3313])).
% 8.05/2.69  tff(c_6268, plain, (![C_121]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_121)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_121)) | ~v1_relat_1(C_121))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_2291, c_46, c_3573])).
% 8.05/2.69  tff(c_6370, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6268, c_14])).
% 8.05/2.69  tff(c_6480, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_319, c_6370])).
% 8.05/2.69  tff(c_6482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_6480])).
% 8.05/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.05/2.69  
% 8.05/2.69  Inference rules
% 8.05/2.69  ----------------------
% 8.05/2.69  #Ref     : 1
% 8.05/2.69  #Sup     : 1409
% 8.05/2.69  #Fact    : 0
% 8.05/2.69  #Define  : 0
% 8.05/2.69  #Split   : 3
% 8.05/2.69  #Chain   : 0
% 8.05/2.69  #Close   : 0
% 8.05/2.69  
% 8.05/2.69  Ordering : KBO
% 8.05/2.69  
% 8.05/2.69  Simplification rules
% 8.05/2.69  ----------------------
% 8.05/2.69  #Subsume      : 9
% 8.05/2.69  #Demod        : 2432
% 8.05/2.69  #Tautology    : 483
% 8.05/2.69  #SimpNegUnit  : 1
% 8.05/2.69  #BackRed      : 14
% 8.05/2.69  
% 8.05/2.69  #Partial instantiations: 0
% 8.05/2.69  #Strategies tried      : 1
% 8.05/2.69  
% 8.05/2.69  Timing (in seconds)
% 8.05/2.69  ----------------------
% 8.05/2.69  Preprocessing        : 0.33
% 8.05/2.69  Parsing              : 0.17
% 8.05/2.69  CNF conversion       : 0.02
% 8.05/2.69  Main loop            : 1.60
% 8.05/2.69  Inferencing          : 0.44
% 8.05/2.69  Reduction            : 0.78
% 8.05/2.69  Demodulation         : 0.64
% 8.05/2.69  BG Simplification    : 0.07
% 8.05/2.69  Subsumption          : 0.24
% 8.05/2.69  Abstraction          : 0.10
% 8.05/2.69  MUC search           : 0.00
% 8.05/2.70  Cooper               : 0.00
% 8.05/2.70  Total                : 1.96
% 8.05/2.70  Index Insertion      : 0.00
% 8.05/2.70  Index Deletion       : 0.00
% 8.05/2.70  Index Matching       : 0.00
% 8.05/2.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
