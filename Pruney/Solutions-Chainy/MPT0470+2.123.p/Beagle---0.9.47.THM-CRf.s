%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:18 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 109 expanded)
%              Number of leaves         :   30 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 186 expanded)
%              Number of equality atoms :   33 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_94,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_36,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_83,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_85,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_1'(A_42),A_42)
      | v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,(
    ! [A_39,B_40] : ~ r2_hidden(A_39,k2_zfmisc_1(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_76])).

tff(c_90,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_85,c_82])).

tff(c_22,plain,(
    ! [A_25,B_26] :
      ( v1_relat_1(k5_relat_1(A_25,B_26))
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_164,plain,(
    ! [A_62,B_63] :
      ( k1_relat_1(k5_relat_1(A_62,B_63)) = k1_relat_1(A_62)
      | ~ r1_tarski(k2_relat_1(A_62),k1_relat_1(B_63))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_173,plain,(
    ! [B_63] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_63)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_63))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_164])).

tff(c_180,plain,(
    ! [B_64] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_64)) = k1_xboole_0
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_6,c_34,c_173])).

tff(c_24,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0(k1_relat_1(A_27))
      | ~ v1_relat_1(A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_192,plain,(
    ! [B_64] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_64))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_64))
      | ~ v1_relat_1(B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_24])).

tff(c_207,plain,(
    ! [B_66] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_66))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_66))
      | ~ v1_relat_1(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_192])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_281,plain,(
    ! [B_69] :
      ( k5_relat_1(k1_xboole_0,B_69) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_69))
      | ~ v1_relat_1(B_69) ) ),
    inference(resolution,[status(thm)],[c_207,c_4])).

tff(c_288,plain,(
    ! [B_26] :
      ( k5_relat_1(k1_xboole_0,B_26) = k1_xboole_0
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_281])).

tff(c_294,plain,(
    ! [B_70] :
      ( k5_relat_1(k1_xboole_0,B_70) = k1_xboole_0
      | ~ v1_relat_1(B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_288])).

tff(c_303,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_294])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_303])).

tff(c_311,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_318,plain,(
    ! [A_72] :
      ( r2_hidden('#skF_1'(A_72),A_72)
      | v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_323,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_318,c_82])).

tff(c_463,plain,(
    ! [B_95,A_96] :
      ( k2_relat_1(k5_relat_1(B_95,A_96)) = k2_relat_1(A_96)
      | ~ r1_tarski(k1_relat_1(A_96),k2_relat_1(B_95))
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_469,plain,(
    ! [B_95] :
      ( k2_relat_1(k5_relat_1(B_95,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_95))
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_463])).

tff(c_479,plain,(
    ! [B_97] :
      ( k2_relat_1(k5_relat_1(B_97,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_6,c_32,c_469])).

tff(c_26,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0(k2_relat_1(A_28))
      | ~ v1_relat_1(A_28)
      | v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_491,plain,(
    ! [B_97] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_97,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_97,k1_xboole_0))
      | ~ v1_relat_1(B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_26])).

tff(c_506,plain,(
    ! [B_98] :
      ( ~ v1_relat_1(k5_relat_1(B_98,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(B_98,k1_xboole_0))
      | ~ v1_relat_1(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_491])).

tff(c_516,plain,(
    ! [B_99] :
      ( k5_relat_1(B_99,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_99,k1_xboole_0))
      | ~ v1_relat_1(B_99) ) ),
    inference(resolution,[status(thm)],[c_506,c_4])).

tff(c_523,plain,(
    ! [A_25] :
      ( k5_relat_1(A_25,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_25) ) ),
    inference(resolution,[status(thm)],[c_22,c_516])).

tff(c_571,plain,(
    ! [A_102] :
      ( k5_relat_1(A_102,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_523])).

tff(c_580,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_571])).

tff(c_587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_580])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:25:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.38  
% 2.58/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.38  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.58/1.38  
% 2.58/1.38  %Foreground sorts:
% 2.58/1.38  
% 2.58/1.38  
% 2.58/1.38  %Background operators:
% 2.58/1.38  
% 2.58/1.38  
% 2.58/1.38  %Foreground operators:
% 2.58/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.58/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.58/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.58/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.58/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.58/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.58/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.58/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.58/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.58/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.58/1.38  
% 2.58/1.40  tff(f_101, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.58/1.40  tff(f_51, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.58/1.40  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.58/1.40  tff(f_41, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.58/1.40  tff(f_57, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.58/1.40  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.58/1.40  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.58/1.40  tff(f_94, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.58/1.40  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.58/1.40  tff(f_65, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.58/1.40  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.58/1.40  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.58/1.40  tff(f_73, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.58/1.40  tff(c_36, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.58/1.40  tff(c_83, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.58/1.40  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.58/1.40  tff(c_85, plain, (![A_42]: (r2_hidden('#skF_1'(A_42), A_42) | v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.58/1.40  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.58/1.40  tff(c_76, plain, (![A_39, B_40]: (~r2_hidden(A_39, k2_zfmisc_1(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.58/1.40  tff(c_82, plain, (![A_3]: (~r2_hidden(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_76])).
% 2.58/1.40  tff(c_90, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_85, c_82])).
% 2.58/1.40  tff(c_22, plain, (![A_25, B_26]: (v1_relat_1(k5_relat_1(A_25, B_26)) | ~v1_relat_1(B_26) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.58/1.40  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.58/1.40  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.58/1.40  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.58/1.40  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.58/1.40  tff(c_164, plain, (![A_62, B_63]: (k1_relat_1(k5_relat_1(A_62, B_63))=k1_relat_1(A_62) | ~r1_tarski(k2_relat_1(A_62), k1_relat_1(B_63)) | ~v1_relat_1(B_63) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.58/1.40  tff(c_173, plain, (![B_63]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_63))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_63)) | ~v1_relat_1(B_63) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_164])).
% 2.58/1.40  tff(c_180, plain, (![B_64]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_64))=k1_xboole_0 | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_6, c_34, c_173])).
% 2.58/1.40  tff(c_24, plain, (![A_27]: (~v1_xboole_0(k1_relat_1(A_27)) | ~v1_relat_1(A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.58/1.40  tff(c_192, plain, (![B_64]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_64)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_64)) | ~v1_relat_1(B_64))), inference(superposition, [status(thm), theory('equality')], [c_180, c_24])).
% 2.58/1.40  tff(c_207, plain, (![B_66]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_66)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_66)) | ~v1_relat_1(B_66))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_192])).
% 2.58/1.40  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.58/1.40  tff(c_281, plain, (![B_69]: (k5_relat_1(k1_xboole_0, B_69)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_69)) | ~v1_relat_1(B_69))), inference(resolution, [status(thm)], [c_207, c_4])).
% 2.58/1.40  tff(c_288, plain, (![B_26]: (k5_relat_1(k1_xboole_0, B_26)=k1_xboole_0 | ~v1_relat_1(B_26) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_281])).
% 2.58/1.40  tff(c_294, plain, (![B_70]: (k5_relat_1(k1_xboole_0, B_70)=k1_xboole_0 | ~v1_relat_1(B_70))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_288])).
% 2.58/1.40  tff(c_303, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_294])).
% 2.58/1.40  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_303])).
% 2.58/1.40  tff(c_311, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.58/1.40  tff(c_318, plain, (![A_72]: (r2_hidden('#skF_1'(A_72), A_72) | v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.58/1.40  tff(c_323, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_318, c_82])).
% 2.58/1.40  tff(c_463, plain, (![B_95, A_96]: (k2_relat_1(k5_relat_1(B_95, A_96))=k2_relat_1(A_96) | ~r1_tarski(k1_relat_1(A_96), k2_relat_1(B_95)) | ~v1_relat_1(B_95) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.58/1.40  tff(c_469, plain, (![B_95]: (k2_relat_1(k5_relat_1(B_95, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_95)) | ~v1_relat_1(B_95) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_463])).
% 2.58/1.40  tff(c_479, plain, (![B_97]: (k2_relat_1(k5_relat_1(B_97, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_97))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_6, c_32, c_469])).
% 2.58/1.40  tff(c_26, plain, (![A_28]: (~v1_xboole_0(k2_relat_1(A_28)) | ~v1_relat_1(A_28) | v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.58/1.40  tff(c_491, plain, (![B_97]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_97, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_97, k1_xboole_0)) | ~v1_relat_1(B_97))), inference(superposition, [status(thm), theory('equality')], [c_479, c_26])).
% 2.58/1.40  tff(c_506, plain, (![B_98]: (~v1_relat_1(k5_relat_1(B_98, k1_xboole_0)) | v1_xboole_0(k5_relat_1(B_98, k1_xboole_0)) | ~v1_relat_1(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_491])).
% 2.58/1.40  tff(c_516, plain, (![B_99]: (k5_relat_1(B_99, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_99, k1_xboole_0)) | ~v1_relat_1(B_99))), inference(resolution, [status(thm)], [c_506, c_4])).
% 2.58/1.40  tff(c_523, plain, (![A_25]: (k5_relat_1(A_25, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_25))), inference(resolution, [status(thm)], [c_22, c_516])).
% 2.58/1.40  tff(c_571, plain, (![A_102]: (k5_relat_1(A_102, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_102))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_523])).
% 2.58/1.40  tff(c_580, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_571])).
% 2.58/1.40  tff(c_587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_311, c_580])).
% 2.58/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.40  
% 2.58/1.40  Inference rules
% 2.58/1.40  ----------------------
% 2.58/1.40  #Ref     : 2
% 2.58/1.40  #Sup     : 115
% 2.58/1.40  #Fact    : 0
% 2.58/1.40  #Define  : 0
% 2.58/1.40  #Split   : 1
% 2.58/1.40  #Chain   : 0
% 2.58/1.40  #Close   : 0
% 2.58/1.40  
% 2.58/1.40  Ordering : KBO
% 2.58/1.40  
% 2.58/1.40  Simplification rules
% 2.58/1.40  ----------------------
% 2.58/1.40  #Subsume      : 6
% 2.58/1.40  #Demod        : 114
% 2.58/1.40  #Tautology    : 72
% 2.58/1.40  #SimpNegUnit  : 2
% 2.58/1.40  #BackRed      : 0
% 2.58/1.40  
% 2.58/1.40  #Partial instantiations: 0
% 2.58/1.40  #Strategies tried      : 1
% 2.58/1.40  
% 2.58/1.40  Timing (in seconds)
% 2.58/1.40  ----------------------
% 2.58/1.40  Preprocessing        : 0.30
% 2.58/1.40  Parsing              : 0.17
% 2.58/1.40  CNF conversion       : 0.02
% 2.58/1.40  Main loop            : 0.27
% 2.58/1.40  Inferencing          : 0.11
% 2.58/1.40  Reduction            : 0.07
% 2.58/1.40  Demodulation         : 0.05
% 2.58/1.40  BG Simplification    : 0.02
% 2.58/1.40  Subsumption          : 0.05
% 2.58/1.40  Abstraction          : 0.01
% 2.58/1.40  MUC search           : 0.00
% 2.58/1.40  Cooper               : 0.00
% 2.58/1.40  Total                : 0.60
% 2.58/1.40  Index Insertion      : 0.00
% 2.58/1.40  Index Deletion       : 0.00
% 2.58/1.40  Index Matching       : 0.00
% 2.58/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
