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
% DateTime   : Thu Dec  3 09:59:01 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 111 expanded)
%              Number of leaves         :   25 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 184 expanded)
%              Number of equality atoms :   38 (  64 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_41,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_43,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_78,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_34,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_61,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    ! [A_6] : k1_subset_1(A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_7] : v1_xboole_0(k1_subset_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_56,plain,(
    ! [A_21] :
      ( v1_relat_1(A_21)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_60,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_37,c_56])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k5_relat_1(A_9,B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_144,plain,(
    ! [A_34,B_35] :
      ( k1_relat_1(k5_relat_1(A_34,B_35)) = k1_relat_1(A_34)
      | ~ r1_tarski(k2_relat_1(A_34),k1_relat_1(B_35))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_150,plain,(
    ! [B_35] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_35)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_35))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_144])).

tff(c_176,plain,(
    ! [B_37] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_37)) = k1_xboole_0
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_8,c_32,c_150])).

tff(c_24,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,k2_zfmisc_1(k1_relat_1(A_11),k2_relat_1(A_11)))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_188,plain,(
    ! [B_37] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,B_37),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_37))))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_24])).

tff(c_325,plain,(
    ! [B_44] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,B_44),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_44))
      | ~ v1_relat_1(B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_188])).

tff(c_96,plain,(
    ! [B_28,A_29] :
      ( B_28 = A_29
      | ~ r1_tarski(B_28,A_29)
      | ~ r1_tarski(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_340,plain,(
    ! [B_45] :
      ( k5_relat_1(k1_xboole_0,B_45) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_45))
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_325,c_101])).

tff(c_347,plain,(
    ! [B_10] :
      ( k5_relat_1(k1_xboole_0,B_10) = k1_xboole_0
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_340])).

tff(c_353,plain,(
    ! [B_46] :
      ( k5_relat_1(k1_xboole_0,B_46) = k1_xboole_0
      | ~ v1_relat_1(B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_347])).

tff(c_362,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_353])).

tff(c_369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_362])).

tff(c_370,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_484,plain,(
    ! [B_60,A_61] :
      ( k2_relat_1(k5_relat_1(B_60,A_61)) = k2_relat_1(A_61)
      | ~ r1_tarski(k1_relat_1(A_61),k2_relat_1(B_60))
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_490,plain,(
    ! [B_60] :
      ( k2_relat_1(k5_relat_1(B_60,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_60))
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_484])).

tff(c_500,plain,(
    ! [B_62] :
      ( k2_relat_1(k5_relat_1(B_62,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_8,c_30,c_490])).

tff(c_512,plain,(
    ! [B_62] :
      ( r1_tarski(k5_relat_1(B_62,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_62,k1_xboole_0)),k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(B_62,k1_xboole_0))
      | ~ v1_relat_1(B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_24])).

tff(c_650,plain,(
    ! [B_69] :
      ( r1_tarski(k5_relat_1(B_69,k1_xboole_0),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_69,k1_xboole_0))
      | ~ v1_relat_1(B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_512])).

tff(c_415,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(B_53,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_420,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_415])).

tff(c_676,plain,(
    ! [B_71] :
      ( k5_relat_1(B_71,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_71,k1_xboole_0))
      | ~ v1_relat_1(B_71) ) ),
    inference(resolution,[status(thm)],[c_650,c_420])).

tff(c_683,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_22,c_676])).

tff(c_689,plain,(
    ! [A_72] :
      ( k5_relat_1(A_72,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_683])).

tff(c_698,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_689])).

tff(c_705,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_698])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.33  
% 2.50/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.33  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.50/1.33  
% 2.50/1.33  %Foreground sorts:
% 2.50/1.33  
% 2.50/1.33  
% 2.50/1.33  %Background operators:
% 2.50/1.33  
% 2.50/1.33  
% 2.50/1.33  %Foreground operators:
% 2.50/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.50/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.50/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.50/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.33  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.50/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.50/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.50/1.33  
% 2.50/1.35  tff(f_85, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.50/1.35  tff(f_41, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.50/1.35  tff(f_43, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_subset_1)).
% 2.50/1.35  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.50/1.35  tff(f_53, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.50/1.35  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.50/1.35  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.50/1.35  tff(f_78, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.50/1.35  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.50/1.35  tff(f_57, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.50/1.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.50/1.35  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.50/1.35  tff(c_34, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.50/1.35  tff(c_61, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 2.50/1.35  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.50/1.35  tff(c_16, plain, (![A_6]: (k1_subset_1(A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.50/1.35  tff(c_18, plain, (![A_7]: (v1_xboole_0(k1_subset_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.50/1.35  tff(c_37, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 2.50/1.35  tff(c_56, plain, (![A_21]: (v1_relat_1(A_21) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.50/1.35  tff(c_60, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_37, c_56])).
% 2.50/1.35  tff(c_22, plain, (![A_9, B_10]: (v1_relat_1(k5_relat_1(A_9, B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.50/1.35  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.50/1.35  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.50/1.35  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.50/1.35  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.50/1.35  tff(c_144, plain, (![A_34, B_35]: (k1_relat_1(k5_relat_1(A_34, B_35))=k1_relat_1(A_34) | ~r1_tarski(k2_relat_1(A_34), k1_relat_1(B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.50/1.35  tff(c_150, plain, (![B_35]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_35))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_144])).
% 2.50/1.35  tff(c_176, plain, (![B_37]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_37))=k1_xboole_0 | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_8, c_32, c_150])).
% 2.50/1.35  tff(c_24, plain, (![A_11]: (r1_tarski(A_11, k2_zfmisc_1(k1_relat_1(A_11), k2_relat_1(A_11))) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.50/1.35  tff(c_188, plain, (![B_37]: (r1_tarski(k5_relat_1(k1_xboole_0, B_37), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_37)))) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_37)) | ~v1_relat_1(B_37))), inference(superposition, [status(thm), theory('equality')], [c_176, c_24])).
% 2.50/1.35  tff(c_325, plain, (![B_44]: (r1_tarski(k5_relat_1(k1_xboole_0, B_44), k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_44)) | ~v1_relat_1(B_44))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_188])).
% 2.50/1.35  tff(c_96, plain, (![B_28, A_29]: (B_28=A_29 | ~r1_tarski(B_28, A_29) | ~r1_tarski(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.35  tff(c_101, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_96])).
% 2.50/1.35  tff(c_340, plain, (![B_45]: (k5_relat_1(k1_xboole_0, B_45)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_45)) | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_325, c_101])).
% 2.50/1.35  tff(c_347, plain, (![B_10]: (k5_relat_1(k1_xboole_0, B_10)=k1_xboole_0 | ~v1_relat_1(B_10) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_340])).
% 2.50/1.35  tff(c_353, plain, (![B_46]: (k5_relat_1(k1_xboole_0, B_46)=k1_xboole_0 | ~v1_relat_1(B_46))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_347])).
% 2.50/1.35  tff(c_362, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_353])).
% 2.50/1.35  tff(c_369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_362])).
% 2.50/1.35  tff(c_370, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 2.50/1.35  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.50/1.35  tff(c_484, plain, (![B_60, A_61]: (k2_relat_1(k5_relat_1(B_60, A_61))=k2_relat_1(A_61) | ~r1_tarski(k1_relat_1(A_61), k2_relat_1(B_60)) | ~v1_relat_1(B_60) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.50/1.35  tff(c_490, plain, (![B_60]: (k2_relat_1(k5_relat_1(B_60, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_60)) | ~v1_relat_1(B_60) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_484])).
% 2.50/1.35  tff(c_500, plain, (![B_62]: (k2_relat_1(k5_relat_1(B_62, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_62))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_8, c_30, c_490])).
% 2.50/1.35  tff(c_512, plain, (![B_62]: (r1_tarski(k5_relat_1(B_62, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_62, k1_xboole_0)), k1_xboole_0)) | ~v1_relat_1(k5_relat_1(B_62, k1_xboole_0)) | ~v1_relat_1(B_62))), inference(superposition, [status(thm), theory('equality')], [c_500, c_24])).
% 2.50/1.35  tff(c_650, plain, (![B_69]: (r1_tarski(k5_relat_1(B_69, k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_69, k1_xboole_0)) | ~v1_relat_1(B_69))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_512])).
% 2.50/1.35  tff(c_415, plain, (![B_53, A_54]: (B_53=A_54 | ~r1_tarski(B_53, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.35  tff(c_420, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_415])).
% 2.50/1.35  tff(c_676, plain, (![B_71]: (k5_relat_1(B_71, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_71, k1_xboole_0)) | ~v1_relat_1(B_71))), inference(resolution, [status(thm)], [c_650, c_420])).
% 2.50/1.35  tff(c_683, plain, (![A_9]: (k5_relat_1(A_9, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_22, c_676])).
% 2.50/1.35  tff(c_689, plain, (![A_72]: (k5_relat_1(A_72, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_683])).
% 2.50/1.35  tff(c_698, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_689])).
% 2.50/1.35  tff(c_705, plain, $false, inference(negUnitSimplification, [status(thm)], [c_370, c_698])).
% 2.50/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.35  
% 2.50/1.35  Inference rules
% 2.50/1.35  ----------------------
% 2.50/1.35  #Ref     : 0
% 2.50/1.35  #Sup     : 142
% 2.50/1.35  #Fact    : 0
% 2.50/1.35  #Define  : 0
% 2.50/1.35  #Split   : 1
% 2.50/1.35  #Chain   : 0
% 2.50/1.35  #Close   : 0
% 2.50/1.35  
% 2.50/1.35  Ordering : KBO
% 2.50/1.35  
% 2.50/1.35  Simplification rules
% 2.50/1.35  ----------------------
% 2.50/1.35  #Subsume      : 6
% 2.50/1.35  #Demod        : 164
% 2.50/1.35  #Tautology    : 93
% 2.50/1.35  #SimpNegUnit  : 2
% 2.50/1.35  #BackRed      : 0
% 2.50/1.35  
% 2.50/1.35  #Partial instantiations: 0
% 2.50/1.35  #Strategies tried      : 1
% 2.50/1.35  
% 2.50/1.35  Timing (in seconds)
% 2.50/1.35  ----------------------
% 2.50/1.35  Preprocessing        : 0.28
% 2.50/1.35  Parsing              : 0.16
% 2.50/1.35  CNF conversion       : 0.02
% 2.50/1.35  Main loop            : 0.29
% 2.50/1.35  Inferencing          : 0.11
% 2.50/1.35  Reduction            : 0.09
% 2.50/1.35  Demodulation         : 0.06
% 2.50/1.35  BG Simplification    : 0.02
% 2.50/1.35  Subsumption          : 0.06
% 2.50/1.35  Abstraction          : 0.01
% 2.50/1.35  MUC search           : 0.00
% 2.50/1.35  Cooper               : 0.00
% 2.50/1.35  Total                : 0.61
% 2.50/1.35  Index Insertion      : 0.00
% 2.50/1.35  Index Deletion       : 0.00
% 2.50/1.35  Index Matching       : 0.00
% 2.50/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
