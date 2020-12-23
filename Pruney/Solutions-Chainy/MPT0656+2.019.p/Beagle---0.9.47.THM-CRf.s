%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:03 EST 2020

% Result     : Theorem 6.41s
% Output     : CNFRefutation 6.58s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 293 expanded)
%              Number of leaves         :   24 ( 120 expanded)
%              Depth                    :   17
%              Number of atoms          :  145 ( 826 expanded)
%              Number of equality atoms :   44 ( 301 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_106,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(c_30,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_16,plain,(
    ! [A_15] :
      ( v1_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_18,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_79,plain,(
    v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_18])).

tff(c_8,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_75,plain,(
    k2_relat_1(k5_relat_1('#skF_1','#skF_2')) = k1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_8])).

tff(c_93,plain,(
    ! [A_26] :
      ( k5_relat_1(A_26,k6_relat_1(k2_relat_1(A_26))) = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_102,plain,
    ( k5_relat_1(k5_relat_1('#skF_1','#skF_2'),k6_relat_1(k1_relat_1('#skF_1'))) = k5_relat_1('#skF_1','#skF_2')
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_93])).

tff(c_112,plain,(
    k5_relat_1(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_2')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_32,c_102])).

tff(c_28,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k2_funct_1(A_18)) = k6_relat_1(k1_relat_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_108,plain,(
    ! [A_11] :
      ( k5_relat_1(k6_relat_1(A_11),k6_relat_1(A_11)) = k6_relat_1(A_11)
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_93])).

tff(c_116,plain,(
    ! [A_11] : k5_relat_1(k6_relat_1(A_11),k6_relat_1(A_11)) = k6_relat_1(A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_108])).

tff(c_155,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_30,B_31)),k2_relat_1(B_31))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_161,plain,(
    ! [A_11] :
      ( r1_tarski(k2_relat_1(k6_relat_1(A_11)),k2_relat_1(k6_relat_1(A_11)))
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_155])).

tff(c_196,plain,(
    ! [A_32] : r1_tarski(A_32,A_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_8,c_8,c_161])).

tff(c_10,plain,(
    ! [A_12,B_13] :
      ( k5_relat_1(k6_relat_1(A_12),B_13) = B_13
      | ~ r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_226,plain,(
    ! [B_34] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_34)),B_34) = B_34
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_196,c_10])).

tff(c_245,plain,
    ( k5_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_226])).

tff(c_258,plain,(
    k5_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_245])).

tff(c_524,plain,(
    ! [A_46,B_47,C_48] :
      ( k5_relat_1(k5_relat_1(A_46,B_47),C_48) = k5_relat_1(A_46,k5_relat_1(B_47,C_48))
      | ~ v1_relat_1(C_48)
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_593,plain,(
    ! [C_48] :
      ( k5_relat_1(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1',C_48)) = k5_relat_1('#skF_1',C_48)
      | ~ v1_relat_1(C_48)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_524])).

tff(c_1043,plain,(
    ! [C_55] :
      ( k5_relat_1(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1',C_55)) = k5_relat_1('#skF_1',C_55)
      | ~ v1_relat_1(C_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_44,c_593])).

tff(c_1091,plain,
    ( k5_relat_1(k5_relat_1('#skF_1','#skF_2'),k6_relat_1(k1_relat_1('#skF_1'))) = k5_relat_1('#skF_1',k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1043])).

tff(c_1123,plain,
    ( k5_relat_1('#skF_1',k2_funct_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_112,c_32,c_1091])).

tff(c_1131,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1123])).

tff(c_1134,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_1131])).

tff(c_1138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1134])).

tff(c_1140,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1123])).

tff(c_275,plain,(
    ! [A_35] :
      ( k2_relat_1(k2_funct_1(A_35)) = k1_relat_1(A_35)
      | ~ v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k6_relat_1(k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1406,plain,(
    ! [A_60] :
      ( k5_relat_1(k2_funct_1(A_60),k6_relat_1(k1_relat_1(A_60))) = k2_funct_1(A_60)
      | ~ v1_relat_1(k2_funct_1(A_60))
      | ~ v2_funct_1(A_60)
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_12])).

tff(c_1430,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1406])).

tff(c_1443,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_1140,c_1430])).

tff(c_34,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26,plain,(
    ! [A_18] :
      ( k5_relat_1(k2_funct_1(A_18),A_18) = k6_relat_1(k2_relat_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5260,plain,(
    ! [A_105,C_106] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_105)),C_106) = k5_relat_1(k2_funct_1(A_105),k5_relat_1(A_105,C_106))
      | ~ v1_relat_1(C_106)
      | ~ v1_relat_1(A_105)
      | ~ v1_relat_1(k2_funct_1(A_105))
      | ~ v2_funct_1(A_105)
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_524])).

tff(c_5624,plain,(
    ! [C_106] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_106) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_106))
      | ~ v1_relat_1(C_106)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_5260])).

tff(c_5805,plain,(
    ! [C_107] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_107) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_107))
      | ~ v1_relat_1(C_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_1140,c_44,c_5624])).

tff(c_201,plain,(
    ! [B_13] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_13)),B_13) = B_13
      | ~ v1_relat_1(B_13) ) ),
    inference(resolution,[status(thm)],[c_196,c_10])).

tff(c_5948,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5805,c_201])).

tff(c_6091,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_1443,c_5948])).

tff(c_6093,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_6091])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:37:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.41/2.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/2.29  
% 6.41/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/2.30  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 6.41/2.30  
% 6.41/2.30  %Foreground sorts:
% 6.41/2.30  
% 6.41/2.30  
% 6.41/2.30  %Background operators:
% 6.41/2.30  
% 6.41/2.30  
% 6.41/2.30  %Foreground operators:
% 6.41/2.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.41/2.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.41/2.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.41/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.41/2.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.41/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.41/2.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.41/2.30  tff('#skF_2', type, '#skF_2': $i).
% 6.41/2.30  tff('#skF_1', type, '#skF_1': $i).
% 6.41/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.41/2.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.41/2.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.41/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.41/2.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.41/2.30  
% 6.58/2.31  tff(f_106, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 6.58/2.31  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.58/2.31  tff(f_68, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.58/2.31  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.58/2.31  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 6.58/2.31  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 6.58/2.31  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 6.58/2.31  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 6.58/2.31  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 6.58/2.31  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 6.58/2.31  tff(c_30, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.58/2.31  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.58/2.31  tff(c_44, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.58/2.31  tff(c_42, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.58/2.31  tff(c_36, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.58/2.31  tff(c_16, plain, (![A_15]: (v1_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.58/2.31  tff(c_32, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.58/2.31  tff(c_18, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.58/2.31  tff(c_79, plain, (v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_18])).
% 6.58/2.31  tff(c_8, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.58/2.31  tff(c_75, plain, (k2_relat_1(k5_relat_1('#skF_1', '#skF_2'))=k1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_8])).
% 6.58/2.31  tff(c_93, plain, (![A_26]: (k5_relat_1(A_26, k6_relat_1(k2_relat_1(A_26)))=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.58/2.31  tff(c_102, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), k6_relat_1(k1_relat_1('#skF_1')))=k5_relat_1('#skF_1', '#skF_2') | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_93])).
% 6.58/2.31  tff(c_112, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_2'))=k5_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_32, c_102])).
% 6.58/2.31  tff(c_28, plain, (![A_18]: (k5_relat_1(A_18, k2_funct_1(A_18))=k6_relat_1(k1_relat_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.58/2.31  tff(c_108, plain, (![A_11]: (k5_relat_1(k6_relat_1(A_11), k6_relat_1(A_11))=k6_relat_1(A_11) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_93])).
% 6.58/2.31  tff(c_116, plain, (![A_11]: (k5_relat_1(k6_relat_1(A_11), k6_relat_1(A_11))=k6_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_108])).
% 6.58/2.31  tff(c_155, plain, (![A_30, B_31]: (r1_tarski(k2_relat_1(k5_relat_1(A_30, B_31)), k2_relat_1(B_31)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.58/2.31  tff(c_161, plain, (![A_11]: (r1_tarski(k2_relat_1(k6_relat_1(A_11)), k2_relat_1(k6_relat_1(A_11))) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_155])).
% 6.58/2.31  tff(c_196, plain, (![A_32]: (r1_tarski(A_32, A_32))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_8, c_8, c_161])).
% 6.58/2.31  tff(c_10, plain, (![A_12, B_13]: (k5_relat_1(k6_relat_1(A_12), B_13)=B_13 | ~r1_tarski(k1_relat_1(B_13), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.58/2.31  tff(c_226, plain, (![B_34]: (k5_relat_1(k6_relat_1(k1_relat_1(B_34)), B_34)=B_34 | ~v1_relat_1(B_34))), inference(resolution, [status(thm)], [c_196, c_10])).
% 6.58/2.31  tff(c_245, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_226])).
% 6.58/2.31  tff(c_258, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_245])).
% 6.58/2.31  tff(c_524, plain, (![A_46, B_47, C_48]: (k5_relat_1(k5_relat_1(A_46, B_47), C_48)=k5_relat_1(A_46, k5_relat_1(B_47, C_48)) | ~v1_relat_1(C_48) | ~v1_relat_1(B_47) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.58/2.31  tff(c_593, plain, (![C_48]: (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', C_48))=k5_relat_1('#skF_1', C_48) | ~v1_relat_1(C_48) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_258, c_524])).
% 6.58/2.31  tff(c_1043, plain, (![C_55]: (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', C_55))=k5_relat_1('#skF_1', C_55) | ~v1_relat_1(C_55))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_44, c_593])).
% 6.58/2.31  tff(c_1091, plain, (k5_relat_1(k5_relat_1('#skF_1', '#skF_2'), k6_relat_1(k1_relat_1('#skF_1')))=k5_relat_1('#skF_1', k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_1043])).
% 6.58/2.31  tff(c_1123, plain, (k5_relat_1('#skF_1', k2_funct_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_112, c_32, c_1091])).
% 6.58/2.31  tff(c_1131, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1123])).
% 6.58/2.31  tff(c_1134, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_1131])).
% 6.58/2.31  tff(c_1138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1134])).
% 6.58/2.31  tff(c_1140, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1123])).
% 6.58/2.31  tff(c_275, plain, (![A_35]: (k2_relat_1(k2_funct_1(A_35))=k1_relat_1(A_35) | ~v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.58/2.31  tff(c_12, plain, (![A_14]: (k5_relat_1(A_14, k6_relat_1(k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.58/2.31  tff(c_1406, plain, (![A_60]: (k5_relat_1(k2_funct_1(A_60), k6_relat_1(k1_relat_1(A_60)))=k2_funct_1(A_60) | ~v1_relat_1(k2_funct_1(A_60)) | ~v2_funct_1(A_60) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(superposition, [status(thm), theory('equality')], [c_275, c_12])).
% 6.58/2.31  tff(c_1430, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_1406])).
% 6.58/2.31  tff(c_1443, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_1140, c_1430])).
% 6.58/2.31  tff(c_34, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.58/2.31  tff(c_26, plain, (![A_18]: (k5_relat_1(k2_funct_1(A_18), A_18)=k6_relat_1(k2_relat_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.58/2.31  tff(c_5260, plain, (![A_105, C_106]: (k5_relat_1(k6_relat_1(k2_relat_1(A_105)), C_106)=k5_relat_1(k2_funct_1(A_105), k5_relat_1(A_105, C_106)) | ~v1_relat_1(C_106) | ~v1_relat_1(A_105) | ~v1_relat_1(k2_funct_1(A_105)) | ~v2_funct_1(A_105) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(superposition, [status(thm), theory('equality')], [c_26, c_524])).
% 6.58/2.31  tff(c_5624, plain, (![C_106]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_106)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_106)) | ~v1_relat_1(C_106) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_5260])).
% 6.58/2.31  tff(c_5805, plain, (![C_107]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_107)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_107)) | ~v1_relat_1(C_107))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_1140, c_44, c_5624])).
% 6.58/2.31  tff(c_201, plain, (![B_13]: (k5_relat_1(k6_relat_1(k1_relat_1(B_13)), B_13)=B_13 | ~v1_relat_1(B_13))), inference(resolution, [status(thm)], [c_196, c_10])).
% 6.58/2.31  tff(c_5948, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5805, c_201])).
% 6.58/2.31  tff(c_6091, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_1443, c_5948])).
% 6.58/2.31  tff(c_6093, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_6091])).
% 6.58/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.58/2.31  
% 6.58/2.31  Inference rules
% 6.58/2.31  ----------------------
% 6.58/2.31  #Ref     : 0
% 6.58/2.31  #Sup     : 1233
% 6.58/2.31  #Fact    : 0
% 6.58/2.31  #Define  : 0
% 6.58/2.31  #Split   : 7
% 6.58/2.31  #Chain   : 0
% 6.58/2.31  #Close   : 0
% 6.58/2.31  
% 6.58/2.31  Ordering : KBO
% 6.58/2.31  
% 6.58/2.31  Simplification rules
% 6.58/2.31  ----------------------
% 6.58/2.31  #Subsume      : 151
% 6.58/2.31  #Demod        : 2866
% 6.58/2.31  #Tautology    : 538
% 6.58/2.31  #SimpNegUnit  : 1
% 6.58/2.31  #BackRed      : 5
% 6.58/2.31  
% 6.58/2.31  #Partial instantiations: 0
% 6.58/2.31  #Strategies tried      : 1
% 6.58/2.31  
% 6.58/2.31  Timing (in seconds)
% 6.58/2.31  ----------------------
% 6.58/2.31  Preprocessing        : 0.33
% 6.58/2.31  Parsing              : 0.18
% 6.58/2.31  CNF conversion       : 0.02
% 6.58/2.32  Main loop            : 1.20
% 6.58/2.32  Inferencing          : 0.39
% 6.58/2.32  Reduction            : 0.51
% 6.58/2.32  Demodulation         : 0.40
% 6.58/2.32  BG Simplification    : 0.04
% 6.58/2.32  Subsumption          : 0.20
% 6.58/2.32  Abstraction          : 0.07
% 6.58/2.32  MUC search           : 0.00
% 6.58/2.32  Cooper               : 0.00
% 6.58/2.32  Total                : 1.56
% 6.58/2.32  Index Insertion      : 0.00
% 6.58/2.32  Index Deletion       : 0.00
% 6.58/2.32  Index Matching       : 0.00
% 6.58/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
