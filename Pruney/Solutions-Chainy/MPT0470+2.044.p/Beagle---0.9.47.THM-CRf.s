%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:07 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   66 (  96 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  102 ( 154 expanded)
%              Number of equality atoms :   37 (  57 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_34,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_79,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_38,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_81,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_82,plain,(
    ! [A_26] :
      ( v1_relat_1(A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_86,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_82])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k5_relat_1(A_12,B_13))
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_20,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_211,plain,(
    ! [A_44,B_45] :
      ( k1_relat_1(k5_relat_1(A_44,B_45)) = k1_relat_1(A_44)
      | ~ r1_tarski(k2_relat_1(A_44),k1_relat_1(B_45))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_220,plain,(
    ! [B_45] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_45)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_45))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_211])).

tff(c_335,plain,(
    ! [B_49] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_49)) = k1_xboole_0
      | ~ v1_relat_1(B_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_12,c_36,c_220])).

tff(c_28,plain,(
    ! [A_14] :
      ( k3_xboole_0(A_14,k2_zfmisc_1(k1_relat_1(A_14),k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_344,plain,(
    ! [B_49] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_49),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_49)))) = k5_relat_1(k1_xboole_0,B_49)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_49))
      | ~ v1_relat_1(B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_28])).

tff(c_356,plain,(
    ! [B_50] :
      ( k5_relat_1(k1_xboole_0,B_50) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_50))
      | ~ v1_relat_1(B_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20,c_344])).

tff(c_363,plain,(
    ! [B_13] :
      ( k5_relat_1(k1_xboole_0,B_13) = k1_xboole_0
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_356])).

tff(c_369,plain,(
    ! [B_51] :
      ( k5_relat_1(k1_xboole_0,B_51) = k1_xboole_0
      | ~ v1_relat_1(B_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_363])).

tff(c_378,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_369])).

tff(c_385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_378])).

tff(c_386,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_388,plain,(
    ! [A_52] :
      ( v1_relat_1(A_52)
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_392,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_388])).

tff(c_18,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_474,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_65,B_66)),k2_relat_1(B_66))
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_482,plain,(
    ! [A_65] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_65,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_474])).

tff(c_520,plain,(
    ! [A_70] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_70,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_482])).

tff(c_426,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_431,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_426])).

tff(c_530,plain,(
    ! [A_71] :
      ( k2_relat_1(k5_relat_1(A_71,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_520,c_431])).

tff(c_548,plain,(
    ! [A_71] :
      ( k3_xboole_0(k5_relat_1(A_71,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_71,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(A_71,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_71,k1_xboole_0))
      | ~ v1_relat_1(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_28])).

tff(c_631,plain,(
    ! [A_76] :
      ( k5_relat_1(A_76,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_76,k1_xboole_0))
      | ~ v1_relat_1(A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_18,c_548])).

tff(c_638,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_12) ) ),
    inference(resolution,[status(thm)],[c_26,c_631])).

tff(c_663,plain,(
    ! [A_78] :
      ( k5_relat_1(A_78,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_638])).

tff(c_672,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_663])).

tff(c_679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_386,c_672])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.31  
% 2.11/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.32  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.11/1.32  
% 2.11/1.32  %Foreground sorts:
% 2.11/1.32  
% 2.11/1.32  
% 2.11/1.32  %Background operators:
% 2.11/1.32  
% 2.11/1.32  
% 2.11/1.32  %Foreground operators:
% 2.11/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.11/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.11/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.11/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.11/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.11/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.11/1.32  
% 2.11/1.33  tff(f_86, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.11/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.11/1.33  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.11/1.33  tff(f_56, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.11/1.33  tff(f_34, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.11/1.33  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.11/1.33  tff(f_36, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.11/1.33  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.11/1.33  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.11/1.33  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 2.11/1.33  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.11/1.33  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.11/1.33  tff(c_38, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.11/1.33  tff(c_81, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 2.11/1.33  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.11/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.11/1.33  tff(c_82, plain, (![A_26]: (v1_relat_1(A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.11/1.33  tff(c_86, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_82])).
% 2.11/1.33  tff(c_26, plain, (![A_12, B_13]: (v1_relat_1(k5_relat_1(A_12, B_13)) | ~v1_relat_1(B_13) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.33  tff(c_10, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.11/1.33  tff(c_20, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.11/1.33  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.11/1.33  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.11/1.33  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.11/1.33  tff(c_211, plain, (![A_44, B_45]: (k1_relat_1(k5_relat_1(A_44, B_45))=k1_relat_1(A_44) | ~r1_tarski(k2_relat_1(A_44), k1_relat_1(B_45)) | ~v1_relat_1(B_45) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.11/1.33  tff(c_220, plain, (![B_45]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_45))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_45)) | ~v1_relat_1(B_45) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_211])).
% 2.11/1.33  tff(c_335, plain, (![B_49]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_49))=k1_xboole_0 | ~v1_relat_1(B_49))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_12, c_36, c_220])).
% 2.11/1.33  tff(c_28, plain, (![A_14]: (k3_xboole_0(A_14, k2_zfmisc_1(k1_relat_1(A_14), k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.11/1.33  tff(c_344, plain, (![B_49]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_49), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_49))))=k5_relat_1(k1_xboole_0, B_49) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_49)) | ~v1_relat_1(B_49))), inference(superposition, [status(thm), theory('equality')], [c_335, c_28])).
% 2.11/1.33  tff(c_356, plain, (![B_50]: (k5_relat_1(k1_xboole_0, B_50)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_50)) | ~v1_relat_1(B_50))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20, c_344])).
% 2.11/1.33  tff(c_363, plain, (![B_13]: (k5_relat_1(k1_xboole_0, B_13)=k1_xboole_0 | ~v1_relat_1(B_13) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_356])).
% 2.11/1.33  tff(c_369, plain, (![B_51]: (k5_relat_1(k1_xboole_0, B_51)=k1_xboole_0 | ~v1_relat_1(B_51))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_363])).
% 2.11/1.33  tff(c_378, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_369])).
% 2.11/1.33  tff(c_385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_378])).
% 2.11/1.33  tff(c_386, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.11/1.33  tff(c_388, plain, (![A_52]: (v1_relat_1(A_52) | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.11/1.33  tff(c_392, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_388])).
% 2.11/1.33  tff(c_18, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.11/1.33  tff(c_474, plain, (![A_65, B_66]: (r1_tarski(k2_relat_1(k5_relat_1(A_65, B_66)), k2_relat_1(B_66)) | ~v1_relat_1(B_66) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.11/1.33  tff(c_482, plain, (![A_65]: (r1_tarski(k2_relat_1(k5_relat_1(A_65, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_65))), inference(superposition, [status(thm), theory('equality')], [c_34, c_474])).
% 2.11/1.33  tff(c_520, plain, (![A_70]: (r1_tarski(k2_relat_1(k5_relat_1(A_70, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_392, c_482])).
% 2.11/1.33  tff(c_426, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.11/1.33  tff(c_431, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_426])).
% 2.11/1.33  tff(c_530, plain, (![A_71]: (k2_relat_1(k5_relat_1(A_71, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_520, c_431])).
% 2.11/1.33  tff(c_548, plain, (![A_71]: (k3_xboole_0(k5_relat_1(A_71, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_71, k1_xboole_0)), k1_xboole_0))=k5_relat_1(A_71, k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_71, k1_xboole_0)) | ~v1_relat_1(A_71))), inference(superposition, [status(thm), theory('equality')], [c_530, c_28])).
% 2.11/1.33  tff(c_631, plain, (![A_76]: (k5_relat_1(A_76, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_76, k1_xboole_0)) | ~v1_relat_1(A_76))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_18, c_548])).
% 2.11/1.33  tff(c_638, plain, (![A_12]: (k5_relat_1(A_12, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_12))), inference(resolution, [status(thm)], [c_26, c_631])).
% 2.11/1.33  tff(c_663, plain, (![A_78]: (k5_relat_1(A_78, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_392, c_638])).
% 2.11/1.33  tff(c_672, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_663])).
% 2.11/1.33  tff(c_679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_386, c_672])).
% 2.11/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.33  
% 2.11/1.33  Inference rules
% 2.11/1.33  ----------------------
% 2.11/1.33  #Ref     : 0
% 2.11/1.33  #Sup     : 137
% 2.11/1.33  #Fact    : 0
% 2.11/1.33  #Define  : 0
% 2.11/1.33  #Split   : 1
% 2.11/1.33  #Chain   : 0
% 2.11/1.33  #Close   : 0
% 2.11/1.33  
% 2.11/1.33  Ordering : KBO
% 2.11/1.33  
% 2.11/1.33  Simplification rules
% 2.11/1.33  ----------------------
% 2.11/1.33  #Subsume      : 7
% 2.11/1.33  #Demod        : 141
% 2.11/1.33  #Tautology    : 93
% 2.11/1.33  #SimpNegUnit  : 2
% 2.11/1.33  #BackRed      : 0
% 2.11/1.33  
% 2.11/1.33  #Partial instantiations: 0
% 2.11/1.33  #Strategies tried      : 1
% 2.11/1.33  
% 2.11/1.33  Timing (in seconds)
% 2.11/1.33  ----------------------
% 2.57/1.33  Preprocessing        : 0.30
% 2.57/1.33  Parsing              : 0.16
% 2.57/1.33  CNF conversion       : 0.02
% 2.57/1.33  Main loop            : 0.26
% 2.57/1.33  Inferencing          : 0.10
% 2.57/1.33  Reduction            : 0.08
% 2.57/1.33  Demodulation         : 0.06
% 2.57/1.33  BG Simplification    : 0.01
% 2.57/1.33  Subsumption          : 0.05
% 2.57/1.33  Abstraction          : 0.02
% 2.57/1.33  MUC search           : 0.00
% 2.57/1.33  Cooper               : 0.00
% 2.57/1.33  Total                : 0.60
% 2.57/1.33  Index Insertion      : 0.00
% 2.57/1.33  Index Deletion       : 0.00
% 2.57/1.33  Index Matching       : 0.00
% 2.57/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
