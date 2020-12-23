%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:27 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 118 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  118 ( 227 expanded)
%              Number of equality atoms :   32 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(k2_relat_1(B),k1_relat_1(C))
           => r1_tarski(k10_relat_1(B,A),k10_relat_1(k5_relat_1(B,C),k9_relat_1(C,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_1)).

tff(c_28,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_30,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k10_relat_1(B_15,k9_relat_1(B_15,A_14)),A_14)
      | ~ v2_funct_1(B_15)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [A_11] : v1_funct_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_93,plain,(
    ! [B_29,A_30] :
      ( r1_tarski(k10_relat_1(B_29,A_30),k1_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_98,plain,(
    ! [A_9,A_30] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_9),A_30),A_9)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_93])).

tff(c_101,plain,(
    ! [A_9,A_30] : r1_tarski(k10_relat_1(k6_relat_1(A_9),A_30),A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_98])).

tff(c_209,plain,(
    ! [B_46,A_47] :
      ( k9_relat_1(B_46,k10_relat_1(B_46,A_47)) = A_47
      | ~ r1_tarski(A_47,k2_relat_1(B_46))
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_398,plain,(
    ! [B_56,A_57] :
      ( k9_relat_1(B_56,k10_relat_1(B_56,k10_relat_1(k6_relat_1(k2_relat_1(B_56)),A_57))) = k10_relat_1(k6_relat_1(k2_relat_1(B_56)),A_57)
      | ~ v1_funct_1(B_56)
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_101,c_209])).

tff(c_437,plain,(
    ! [A_9,A_57] :
      ( k9_relat_1(k6_relat_1(A_9),k10_relat_1(k6_relat_1(A_9),k10_relat_1(k6_relat_1(A_9),A_57))) = k10_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_9))),A_57)
      | ~ v1_funct_1(k6_relat_1(A_9))
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_398])).

tff(c_450,plain,(
    ! [A_9,A_57] : k9_relat_1(k6_relat_1(A_9),k10_relat_1(k6_relat_1(A_9),k10_relat_1(k6_relat_1(A_9),A_57))) = k10_relat_1(k6_relat_1(A_9),A_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_14,c_437])).

tff(c_628,plain,(
    ! [A_66,A_67] : k9_relat_1(k6_relat_1(A_66),k10_relat_1(k6_relat_1(A_66),k10_relat_1(k6_relat_1(A_66),A_67))) = k10_relat_1(k6_relat_1(A_66),A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_14,c_437])).

tff(c_59,plain,(
    ! [A_25] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_25)),A_25) = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_68,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_relat_1(A_9),k6_relat_1(A_9)) = k6_relat_1(A_9)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_59])).

tff(c_72,plain,(
    ! [A_9] : k5_relat_1(k6_relat_1(A_9),k6_relat_1(A_9)) = k6_relat_1(A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_68])).

tff(c_111,plain,(
    ! [B_37,C_38,A_39] :
      ( k9_relat_1(k5_relat_1(B_37,C_38),A_39) = k9_relat_1(C_38,k9_relat_1(B_37,A_39))
      | ~ v1_relat_1(C_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_123,plain,(
    ! [A_9,A_39] :
      ( k9_relat_1(k6_relat_1(A_9),k9_relat_1(k6_relat_1(A_9),A_39)) = k9_relat_1(k6_relat_1(A_9),A_39)
      | ~ v1_relat_1(k6_relat_1(A_9))
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_111])).

tff(c_130,plain,(
    ! [A_9,A_39] : k9_relat_1(k6_relat_1(A_9),k9_relat_1(k6_relat_1(A_9),A_39)) = k9_relat_1(k6_relat_1(A_9),A_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_123])).

tff(c_653,plain,(
    ! [A_66,A_67] : k9_relat_1(k6_relat_1(A_66),k10_relat_1(k6_relat_1(A_66),k10_relat_1(k6_relat_1(A_66),A_67))) = k9_relat_1(k6_relat_1(A_66),k10_relat_1(k6_relat_1(A_66),A_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_130])).

tff(c_674,plain,(
    ! [A_66,A_67] : k9_relat_1(k6_relat_1(A_66),k10_relat_1(k6_relat_1(A_66),A_67)) = k10_relat_1(k6_relat_1(A_66),A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_653])).

tff(c_217,plain,(
    ! [A_9,A_47] :
      ( k9_relat_1(k6_relat_1(A_9),k10_relat_1(k6_relat_1(A_9),A_47)) = A_47
      | ~ r1_tarski(A_47,A_9)
      | ~ v1_funct_1(k6_relat_1(A_9))
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_209])).

tff(c_224,plain,(
    ! [A_9,A_47] :
      ( k9_relat_1(k6_relat_1(A_9),k10_relat_1(k6_relat_1(A_9),A_47)) = A_47
      | ~ r1_tarski(A_47,A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_217])).

tff(c_919,plain,(
    ! [A_73,A_74] :
      ( k10_relat_1(k6_relat_1(A_73),A_74) = A_74
      | ~ r1_tarski(A_74,A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_224])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_10] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_10)),A_10) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_247,plain,(
    ! [B_50,A_51,C_52] :
      ( r1_tarski(k10_relat_1(B_50,A_51),k10_relat_1(k5_relat_1(B_50,C_52),k9_relat_1(C_52,A_51)))
      | ~ r1_tarski(k2_relat_1(B_50),k1_relat_1(C_52))
      | ~ v1_relat_1(C_52)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_267,plain,(
    ! [A_10,A_51] :
      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(A_10)),A_51),k10_relat_1(A_10,k9_relat_1(A_10,A_51)))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(A_10))),k1_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(A_10)))
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_247])).

tff(c_276,plain,(
    ! [A_10,A_51] :
      ( r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(A_10)),A_51),k10_relat_1(A_10,k9_relat_1(A_10,A_51)))
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6,c_14,c_267])).

tff(c_1970,plain,(
    ! [A_96,A_97] :
      ( r1_tarski(A_96,k10_relat_1(A_97,k9_relat_1(A_97,A_96)))
      | ~ v1_relat_1(A_97)
      | ~ r1_tarski(A_96,k1_relat_1(A_97)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_919,c_276])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2159,plain,(
    ! [A_103,A_104] :
      ( k10_relat_1(A_103,k9_relat_1(A_103,A_104)) = A_104
      | ~ r1_tarski(k10_relat_1(A_103,k9_relat_1(A_103,A_104)),A_104)
      | ~ v1_relat_1(A_103)
      | ~ r1_tarski(A_104,k1_relat_1(A_103)) ) ),
    inference(resolution,[status(thm)],[c_1970,c_2])).

tff(c_2677,plain,(
    ! [B_115,A_116] :
      ( k10_relat_1(B_115,k9_relat_1(B_115,A_116)) = A_116
      | ~ r1_tarski(A_116,k1_relat_1(B_115))
      | ~ v2_funct_1(B_115)
      | ~ v1_funct_1(B_115)
      | ~ v1_relat_1(B_115) ) ),
    inference(resolution,[status(thm)],[c_24,c_2159])).

tff(c_2698,plain,
    ( k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_2677])).

tff(c_2712,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_2698])).

tff(c_2714,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2712])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:50:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.06/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.69  
% 4.06/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.70  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.06/1.70  
% 4.06/1.70  %Foreground sorts:
% 4.06/1.70  
% 4.06/1.70  
% 4.06/1.70  %Background operators:
% 4.06/1.70  
% 4.06/1.70  
% 4.06/1.70  %Foreground operators:
% 4.06/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.06/1.70  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.06/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.06/1.70  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.06/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.06/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.06/1.70  tff('#skF_2', type, '#skF_2': $i).
% 4.06/1.70  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.06/1.70  tff('#skF_1', type, '#skF_1': $i).
% 4.06/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.06/1.70  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.06/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.06/1.70  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.06/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.06/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.06/1.70  
% 4.06/1.71  tff(f_90, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 4.06/1.71  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 4.06/1.71  tff(f_54, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.06/1.71  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.06/1.71  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 4.06/1.71  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 4.06/1.71  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 4.06/1.71  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 4.06/1.71  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.06/1.71  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(k2_relat_1(B), k1_relat_1(C)) => r1_tarski(k10_relat_1(B, A), k10_relat_1(k5_relat_1(B, C), k9_relat_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_funct_1)).
% 4.06/1.71  tff(c_28, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.06/1.71  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.06/1.71  tff(c_34, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.06/1.71  tff(c_30, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.06/1.71  tff(c_32, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.06/1.71  tff(c_24, plain, (![B_15, A_14]: (r1_tarski(k10_relat_1(B_15, k9_relat_1(B_15, A_14)), A_14) | ~v2_funct_1(B_15) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.06/1.71  tff(c_18, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.06/1.71  tff(c_20, plain, (![A_11]: (v1_funct_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.06/1.71  tff(c_14, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.06/1.71  tff(c_12, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.06/1.71  tff(c_93, plain, (![B_29, A_30]: (r1_tarski(k10_relat_1(B_29, A_30), k1_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.06/1.71  tff(c_98, plain, (![A_9, A_30]: (r1_tarski(k10_relat_1(k6_relat_1(A_9), A_30), A_9) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_93])).
% 4.06/1.71  tff(c_101, plain, (![A_9, A_30]: (r1_tarski(k10_relat_1(k6_relat_1(A_9), A_30), A_9))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_98])).
% 4.06/1.71  tff(c_209, plain, (![B_46, A_47]: (k9_relat_1(B_46, k10_relat_1(B_46, A_47))=A_47 | ~r1_tarski(A_47, k2_relat_1(B_46)) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.06/1.71  tff(c_398, plain, (![B_56, A_57]: (k9_relat_1(B_56, k10_relat_1(B_56, k10_relat_1(k6_relat_1(k2_relat_1(B_56)), A_57)))=k10_relat_1(k6_relat_1(k2_relat_1(B_56)), A_57) | ~v1_funct_1(B_56) | ~v1_relat_1(B_56))), inference(resolution, [status(thm)], [c_101, c_209])).
% 4.06/1.71  tff(c_437, plain, (![A_9, A_57]: (k9_relat_1(k6_relat_1(A_9), k10_relat_1(k6_relat_1(A_9), k10_relat_1(k6_relat_1(A_9), A_57)))=k10_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_9))), A_57) | ~v1_funct_1(k6_relat_1(A_9)) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_398])).
% 4.06/1.71  tff(c_450, plain, (![A_9, A_57]: (k9_relat_1(k6_relat_1(A_9), k10_relat_1(k6_relat_1(A_9), k10_relat_1(k6_relat_1(A_9), A_57)))=k10_relat_1(k6_relat_1(A_9), A_57))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_14, c_437])).
% 4.06/1.71  tff(c_628, plain, (![A_66, A_67]: (k9_relat_1(k6_relat_1(A_66), k10_relat_1(k6_relat_1(A_66), k10_relat_1(k6_relat_1(A_66), A_67)))=k10_relat_1(k6_relat_1(A_66), A_67))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_14, c_437])).
% 4.06/1.71  tff(c_59, plain, (![A_25]: (k5_relat_1(k6_relat_1(k1_relat_1(A_25)), A_25)=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.06/1.71  tff(c_68, plain, (![A_9]: (k5_relat_1(k6_relat_1(A_9), k6_relat_1(A_9))=k6_relat_1(A_9) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_59])).
% 4.06/1.71  tff(c_72, plain, (![A_9]: (k5_relat_1(k6_relat_1(A_9), k6_relat_1(A_9))=k6_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_68])).
% 4.06/1.71  tff(c_111, plain, (![B_37, C_38, A_39]: (k9_relat_1(k5_relat_1(B_37, C_38), A_39)=k9_relat_1(C_38, k9_relat_1(B_37, A_39)) | ~v1_relat_1(C_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.06/1.71  tff(c_123, plain, (![A_9, A_39]: (k9_relat_1(k6_relat_1(A_9), k9_relat_1(k6_relat_1(A_9), A_39))=k9_relat_1(k6_relat_1(A_9), A_39) | ~v1_relat_1(k6_relat_1(A_9)) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_111])).
% 4.06/1.71  tff(c_130, plain, (![A_9, A_39]: (k9_relat_1(k6_relat_1(A_9), k9_relat_1(k6_relat_1(A_9), A_39))=k9_relat_1(k6_relat_1(A_9), A_39))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_123])).
% 4.06/1.71  tff(c_653, plain, (![A_66, A_67]: (k9_relat_1(k6_relat_1(A_66), k10_relat_1(k6_relat_1(A_66), k10_relat_1(k6_relat_1(A_66), A_67)))=k9_relat_1(k6_relat_1(A_66), k10_relat_1(k6_relat_1(A_66), A_67)))), inference(superposition, [status(thm), theory('equality')], [c_628, c_130])).
% 4.06/1.71  tff(c_674, plain, (![A_66, A_67]: (k9_relat_1(k6_relat_1(A_66), k10_relat_1(k6_relat_1(A_66), A_67))=k10_relat_1(k6_relat_1(A_66), A_67))), inference(demodulation, [status(thm), theory('equality')], [c_450, c_653])).
% 4.06/1.71  tff(c_217, plain, (![A_9, A_47]: (k9_relat_1(k6_relat_1(A_9), k10_relat_1(k6_relat_1(A_9), A_47))=A_47 | ~r1_tarski(A_47, A_9) | ~v1_funct_1(k6_relat_1(A_9)) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_209])).
% 4.06/1.71  tff(c_224, plain, (![A_9, A_47]: (k9_relat_1(k6_relat_1(A_9), k10_relat_1(k6_relat_1(A_9), A_47))=A_47 | ~r1_tarski(A_47, A_9))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_217])).
% 4.06/1.71  tff(c_919, plain, (![A_73, A_74]: (k10_relat_1(k6_relat_1(A_73), A_74)=A_74 | ~r1_tarski(A_74, A_73))), inference(demodulation, [status(thm), theory('equality')], [c_674, c_224])).
% 4.06/1.71  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.06/1.71  tff(c_16, plain, (![A_10]: (k5_relat_1(k6_relat_1(k1_relat_1(A_10)), A_10)=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.06/1.71  tff(c_247, plain, (![B_50, A_51, C_52]: (r1_tarski(k10_relat_1(B_50, A_51), k10_relat_1(k5_relat_1(B_50, C_52), k9_relat_1(C_52, A_51))) | ~r1_tarski(k2_relat_1(B_50), k1_relat_1(C_52)) | ~v1_relat_1(C_52) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.06/1.71  tff(c_267, plain, (![A_10, A_51]: (r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(A_10)), A_51), k10_relat_1(A_10, k9_relat_1(A_10, A_51))) | ~r1_tarski(k2_relat_1(k6_relat_1(k1_relat_1(A_10))), k1_relat_1(A_10)) | ~v1_relat_1(A_10) | ~v1_relat_1(k6_relat_1(k1_relat_1(A_10))) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_16, c_247])).
% 4.06/1.71  tff(c_276, plain, (![A_10, A_51]: (r1_tarski(k10_relat_1(k6_relat_1(k1_relat_1(A_10)), A_51), k10_relat_1(A_10, k9_relat_1(A_10, A_51))) | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6, c_14, c_267])).
% 4.06/1.71  tff(c_1970, plain, (![A_96, A_97]: (r1_tarski(A_96, k10_relat_1(A_97, k9_relat_1(A_97, A_96))) | ~v1_relat_1(A_97) | ~r1_tarski(A_96, k1_relat_1(A_97)))), inference(superposition, [status(thm), theory('equality')], [c_919, c_276])).
% 4.06/1.71  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.06/1.71  tff(c_2159, plain, (![A_103, A_104]: (k10_relat_1(A_103, k9_relat_1(A_103, A_104))=A_104 | ~r1_tarski(k10_relat_1(A_103, k9_relat_1(A_103, A_104)), A_104) | ~v1_relat_1(A_103) | ~r1_tarski(A_104, k1_relat_1(A_103)))), inference(resolution, [status(thm)], [c_1970, c_2])).
% 4.06/1.71  tff(c_2677, plain, (![B_115, A_116]: (k10_relat_1(B_115, k9_relat_1(B_115, A_116))=A_116 | ~r1_tarski(A_116, k1_relat_1(B_115)) | ~v2_funct_1(B_115) | ~v1_funct_1(B_115) | ~v1_relat_1(B_115))), inference(resolution, [status(thm)], [c_24, c_2159])).
% 4.06/1.71  tff(c_2698, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_2677])).
% 4.06/1.71  tff(c_2712, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_2698])).
% 4.06/1.71  tff(c_2714, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2712])).
% 4.06/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.71  
% 4.06/1.71  Inference rules
% 4.06/1.71  ----------------------
% 4.06/1.71  #Ref     : 0
% 4.06/1.71  #Sup     : 560
% 4.06/1.71  #Fact    : 0
% 4.06/1.71  #Define  : 0
% 4.06/1.71  #Split   : 1
% 4.06/1.71  #Chain   : 0
% 4.06/1.71  #Close   : 0
% 4.06/1.71  
% 4.06/1.71  Ordering : KBO
% 4.06/1.71  
% 4.06/1.71  Simplification rules
% 4.06/1.71  ----------------------
% 4.06/1.71  #Subsume      : 69
% 4.06/1.71  #Demod        : 1141
% 4.06/1.71  #Tautology    : 253
% 4.06/1.71  #SimpNegUnit  : 1
% 4.06/1.71  #BackRed      : 4
% 4.06/1.71  
% 4.06/1.71  #Partial instantiations: 0
% 4.06/1.71  #Strategies tried      : 1
% 4.06/1.71  
% 4.06/1.71  Timing (in seconds)
% 4.06/1.71  ----------------------
% 4.06/1.72  Preprocessing        : 0.30
% 4.06/1.72  Parsing              : 0.17
% 4.06/1.72  CNF conversion       : 0.02
% 4.06/1.72  Main loop            : 0.65
% 4.06/1.72  Inferencing          : 0.22
% 4.06/1.72  Reduction            : 0.25
% 4.06/1.72  Demodulation         : 0.20
% 4.06/1.72  BG Simplification    : 0.03
% 4.06/1.72  Subsumption          : 0.11
% 4.06/1.72  Abstraction          : 0.04
% 4.06/1.72  MUC search           : 0.00
% 4.06/1.72  Cooper               : 0.00
% 4.06/1.72  Total                : 0.98
% 4.06/1.72  Index Insertion      : 0.00
% 4.06/1.72  Index Deletion       : 0.00
% 4.06/1.72  Index Matching       : 0.00
% 4.06/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
