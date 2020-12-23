%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:21 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 111 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 152 expanded)
%              Number of equality atoms :    5 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    ! [A_33,B_34] : k2_xboole_0(A_33,k3_xboole_0(A_33,B_34)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_87,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_78])).

tff(c_255,plain,(
    ! [A_55,B_56,C_57] : r1_tarski(k2_xboole_0(k3_xboole_0(A_55,B_56),k3_xboole_0(A_55,C_57)),k2_xboole_0(B_56,C_57)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_291,plain,(
    ! [A_10,B_56] : r1_tarski(k2_xboole_0(k3_xboole_0(A_10,B_56),k1_xboole_0),k2_xboole_0(B_56,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_255])).

tff(c_299,plain,(
    ! [A_58,B_59] : r1_tarski(k3_xboole_0(A_58,B_59),B_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_87,c_291])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_200,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_204,plain,(
    ! [A_18,B_19] :
      ( v1_relat_1(A_18)
      | ~ v1_relat_1(B_19)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(resolution,[status(thm)],[c_20,c_200])).

tff(c_309,plain,(
    ! [A_58,B_59] :
      ( v1_relat_1(k3_xboole_0(A_58,B_59))
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_299,c_204])).

tff(c_298,plain,(
    ! [A_10,B_56] : r1_tarski(k3_xboole_0(A_10,B_56),B_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_87,c_291])).

tff(c_453,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(k2_relat_1(A_76),k2_relat_1(B_77))
      | ~ r1_tarski(A_76,B_77)
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_408,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k2_relat_1(A_70),k2_relat_1(B_71))
      | ~ r1_tarski(A_70,B_71)
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_240,plain,(
    ! [A_52,B_53,C_54] :
      ( r1_tarski(A_52,k3_xboole_0(B_53,C_54))
      | ~ r1_tarski(A_52,C_54)
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_254,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_240,c_28])).

tff(c_313,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_411,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_408,c_313])).

tff(c_417,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4,c_411])).

tff(c_421,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_309,c_417])).

tff(c_428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_421])).

tff(c_429,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_456,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_453,c_429])).

tff(c_462,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_298,c_456])).

tff(c_466,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_309,c_462])).

tff(c_473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_466])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.27  
% 2.25/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.27  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.25/1.27  
% 2.25/1.27  %Foreground sorts:
% 2.25/1.27  
% 2.25/1.27  
% 2.25/1.27  %Background operators:
% 2.25/1.27  
% 2.25/1.27  
% 2.25/1.27  %Foreground operators:
% 2.25/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.25/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.25/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.25/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.25/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.25/1.27  
% 2.46/1.29  tff(f_75, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 2.46/1.29  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.46/1.29  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.46/1.29  tff(f_41, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.46/1.29  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.46/1.29  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.46/1.29  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.46/1.29  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.46/1.29  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.46/1.29  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.46/1.29  tff(c_10, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.46/1.29  tff(c_78, plain, (![A_33, B_34]: (k2_xboole_0(A_33, k3_xboole_0(A_33, B_34))=A_33)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.46/1.29  tff(c_87, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(superposition, [status(thm), theory('equality')], [c_10, c_78])).
% 2.46/1.29  tff(c_255, plain, (![A_55, B_56, C_57]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_55, B_56), k3_xboole_0(A_55, C_57)), k2_xboole_0(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.46/1.29  tff(c_291, plain, (![A_10, B_56]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_10, B_56), k1_xboole_0), k2_xboole_0(B_56, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_255])).
% 2.46/1.29  tff(c_299, plain, (![A_58, B_59]: (r1_tarski(k3_xboole_0(A_58, B_59), B_59))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_87, c_291])).
% 2.46/1.29  tff(c_20, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.46/1.29  tff(c_200, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.46/1.29  tff(c_204, plain, (![A_18, B_19]: (v1_relat_1(A_18) | ~v1_relat_1(B_19) | ~r1_tarski(A_18, B_19))), inference(resolution, [status(thm)], [c_20, c_200])).
% 2.46/1.29  tff(c_309, plain, (![A_58, B_59]: (v1_relat_1(k3_xboole_0(A_58, B_59)) | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_299, c_204])).
% 2.46/1.29  tff(c_298, plain, (![A_10, B_56]: (r1_tarski(k3_xboole_0(A_10, B_56), B_56))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_87, c_291])).
% 2.46/1.29  tff(c_453, plain, (![A_76, B_77]: (r1_tarski(k2_relat_1(A_76), k2_relat_1(B_77)) | ~r1_tarski(A_76, B_77) | ~v1_relat_1(B_77) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.46/1.29  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.46/1.29  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.29  tff(c_408, plain, (![A_70, B_71]: (r1_tarski(k2_relat_1(A_70), k2_relat_1(B_71)) | ~r1_tarski(A_70, B_71) | ~v1_relat_1(B_71) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.46/1.29  tff(c_240, plain, (![A_52, B_53, C_54]: (r1_tarski(A_52, k3_xboole_0(B_53, C_54)) | ~r1_tarski(A_52, C_54) | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.46/1.29  tff(c_28, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.46/1.29  tff(c_254, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_240, c_28])).
% 2.46/1.29  tff(c_313, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_254])).
% 2.46/1.29  tff(c_411, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_408, c_313])).
% 2.46/1.29  tff(c_417, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4, c_411])).
% 2.46/1.29  tff(c_421, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_309, c_417])).
% 2.46/1.29  tff(c_428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_421])).
% 2.46/1.29  tff(c_429, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_254])).
% 2.46/1.29  tff(c_456, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_453, c_429])).
% 2.46/1.29  tff(c_462, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_298, c_456])).
% 2.46/1.29  tff(c_466, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_309, c_462])).
% 2.46/1.29  tff(c_473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_466])).
% 2.46/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.29  
% 2.46/1.29  Inference rules
% 2.46/1.29  ----------------------
% 2.46/1.29  #Ref     : 0
% 2.46/1.29  #Sup     : 98
% 2.46/1.29  #Fact    : 0
% 2.46/1.29  #Define  : 0
% 2.46/1.29  #Split   : 3
% 2.46/1.29  #Chain   : 0
% 2.46/1.29  #Close   : 0
% 2.46/1.29  
% 2.46/1.29  Ordering : KBO
% 2.46/1.29  
% 2.46/1.29  Simplification rules
% 2.46/1.29  ----------------------
% 2.46/1.29  #Subsume      : 2
% 2.46/1.29  #Demod        : 89
% 2.46/1.29  #Tautology    : 72
% 2.46/1.29  #SimpNegUnit  : 4
% 2.46/1.29  #BackRed      : 2
% 2.46/1.29  
% 2.46/1.29  #Partial instantiations: 0
% 2.46/1.29  #Strategies tried      : 1
% 2.46/1.29  
% 2.46/1.29  Timing (in seconds)
% 2.46/1.29  ----------------------
% 2.46/1.29  Preprocessing        : 0.30
% 2.46/1.29  Parsing              : 0.16
% 2.46/1.29  CNF conversion       : 0.02
% 2.46/1.29  Main loop            : 0.24
% 2.46/1.29  Inferencing          : 0.09
% 2.46/1.29  Reduction            : 0.09
% 2.46/1.29  Demodulation         : 0.07
% 2.46/1.29  BG Simplification    : 0.01
% 2.46/1.29  Subsumption          : 0.03
% 2.46/1.29  Abstraction          : 0.01
% 2.46/1.29  MUC search           : 0.00
% 2.46/1.29  Cooper               : 0.00
% 2.46/1.29  Total                : 0.56
% 2.46/1.29  Index Insertion      : 0.00
% 2.46/1.29  Index Deletion       : 0.00
% 2.46/1.29  Index Matching       : 0.00
% 2.46/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
