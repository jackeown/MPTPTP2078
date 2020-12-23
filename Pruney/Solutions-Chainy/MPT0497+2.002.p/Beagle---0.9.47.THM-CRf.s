%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:39 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 105 expanded)
%              Number of leaves         :   27 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 154 expanded)
%              Number of equality atoms :   37 (  71 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_129,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,(
    ! [B_27,A_28] : k3_xboole_0(B_27,A_28) = k3_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_120,plain,(
    ! [A_7] : k3_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_82])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_67,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(B_24,A_25)
      | ~ r1_xboole_0(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    ! [A_8] : r1_xboole_0(k1_xboole_0,A_8) ),
    inference(resolution,[status(thm)],[c_12,c_67])).

tff(c_459,plain,(
    ! [A_53,B_54,C_55,D_56] :
      ( ~ r1_xboole_0(A_53,B_54)
      | r1_xboole_0(k2_zfmisc_1(A_53,C_55),k2_zfmisc_1(B_54,D_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_9] :
      ( ~ r1_xboole_0(A_9,A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_484,plain,(
    ! [B_57,D_58] :
      ( k2_zfmisc_1(B_57,D_58) = k1_xboole_0
      | ~ r1_xboole_0(B_57,B_57) ) ),
    inference(resolution,[status(thm)],[c_459,c_16])).

tff(c_507,plain,(
    ! [D_58] : k2_zfmisc_1(k1_xboole_0,D_58) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_484])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k7_relat_1(A_16,B_17))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_280,plain,(
    ! [B_40,A_41] :
      ( k3_xboole_0(k1_relat_1(B_40),A_41) = k1_relat_1(k7_relat_1(B_40,A_41))
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_198,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_42])).

tff(c_206,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_xboole_0(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_223,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_198,c_206])).

tff(c_290,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_223])).

tff(c_332,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_290])).

tff(c_26,plain,(
    ! [A_18] :
      ( k3_xboole_0(A_18,k2_zfmisc_1(k1_relat_1(A_18),k2_relat_1(A_18))) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_343,plain,
    ( k3_xboole_0(k7_relat_1('#skF_2','#skF_1'),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) = k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_26])).

tff(c_413,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_434,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_413])).

tff(c_438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_434])).

tff(c_439,plain,(
    k3_xboole_0(k7_relat_1('#skF_2','#skF_1'),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) = k7_relat_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_760,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_2,c_507,c_439])).

tff(c_761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_760])).

tff(c_763,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_929,plain,(
    ! [B_90,A_91] :
      ( k3_xboole_0(k1_relat_1(B_90),A_91) = k1_relat_1(k7_relat_1(B_90,A_91))
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1241,plain,(
    ! [A_118,B_119] :
      ( k3_xboole_0(A_118,k1_relat_1(B_119)) = k1_relat_1(k7_relat_1(B_119,A_118))
      | ~ v1_relat_1(B_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_929])).

tff(c_810,plain,(
    ! [A_78,B_79] :
      ( r1_xboole_0(A_78,B_79)
      | k3_xboole_0(A_78,B_79) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_762,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_813,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_810,c_762])).

tff(c_821,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_813])).

tff(c_1263,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1241,c_821])).

tff(c_1305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_763,c_1263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.49  
% 3.03/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.49  %$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.03/1.49  
% 3.03/1.49  %Foreground sorts:
% 3.03/1.49  
% 3.03/1.49  
% 3.03/1.49  %Background operators:
% 3.03/1.49  
% 3.03/1.49  
% 3.03/1.49  %Foreground operators:
% 3.03/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.03/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.03/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.03/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.03/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.03/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.03/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.03/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.03/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.03/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.03/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.03/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.03/1.49  
% 3.15/1.51  tff(f_81, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.15/1.51  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.15/1.51  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.15/1.51  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.15/1.51  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.15/1.51  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.15/1.51  tff(f_57, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 3.15/1.51  tff(f_51, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.15/1.51  tff(f_63, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.15/1.51  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.15/1.51  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.15/1.51  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.15/1.51  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.15/1.51  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.15/1.51  tff(c_36, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.15/1.51  tff(c_129, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 3.15/1.51  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.51  tff(c_82, plain, (![B_27, A_28]: (k3_xboole_0(B_27, A_28)=k3_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.51  tff(c_120, plain, (![A_7]: (k3_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_82])).
% 3.15/1.51  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.51  tff(c_12, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.15/1.51  tff(c_67, plain, (![B_24, A_25]: (r1_xboole_0(B_24, A_25) | ~r1_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.15/1.51  tff(c_70, plain, (![A_8]: (r1_xboole_0(k1_xboole_0, A_8))), inference(resolution, [status(thm)], [c_12, c_67])).
% 3.15/1.51  tff(c_459, plain, (![A_53, B_54, C_55, D_56]: (~r1_xboole_0(A_53, B_54) | r1_xboole_0(k2_zfmisc_1(A_53, C_55), k2_zfmisc_1(B_54, D_56)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.15/1.51  tff(c_16, plain, (![A_9]: (~r1_xboole_0(A_9, A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.15/1.51  tff(c_484, plain, (![B_57, D_58]: (k2_zfmisc_1(B_57, D_58)=k1_xboole_0 | ~r1_xboole_0(B_57, B_57))), inference(resolution, [status(thm)], [c_459, c_16])).
% 3.15/1.51  tff(c_507, plain, (![D_58]: (k2_zfmisc_1(k1_xboole_0, D_58)=k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_484])).
% 3.15/1.51  tff(c_24, plain, (![A_16, B_17]: (v1_relat_1(k7_relat_1(A_16, B_17)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.15/1.51  tff(c_280, plain, (![B_40, A_41]: (k3_xboole_0(k1_relat_1(B_40), A_41)=k1_relat_1(k7_relat_1(B_40, A_41)) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.15/1.51  tff(c_42, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.15/1.51  tff(c_198, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_129, c_42])).
% 3.15/1.51  tff(c_206, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.15/1.51  tff(c_223, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_198, c_206])).
% 3.15/1.51  tff(c_290, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_280, c_223])).
% 3.15/1.51  tff(c_332, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_290])).
% 3.15/1.51  tff(c_26, plain, (![A_18]: (k3_xboole_0(A_18, k2_zfmisc_1(k1_relat_1(A_18), k2_relat_1(A_18)))=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.15/1.51  tff(c_343, plain, (k3_xboole_0(k7_relat_1('#skF_2', '#skF_1'), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_332, c_26])).
% 3.15/1.51  tff(c_413, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_343])).
% 3.15/1.51  tff(c_434, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_413])).
% 3.15/1.51  tff(c_438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_434])).
% 3.15/1.51  tff(c_439, plain, (k3_xboole_0(k7_relat_1('#skF_2', '#skF_1'), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))=k7_relat_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_343])).
% 3.15/1.51  tff(c_760, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_120, c_2, c_507, c_439])).
% 3.15/1.51  tff(c_761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_760])).
% 3.15/1.51  tff(c_763, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 3.15/1.51  tff(c_929, plain, (![B_90, A_91]: (k3_xboole_0(k1_relat_1(B_90), A_91)=k1_relat_1(k7_relat_1(B_90, A_91)) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.15/1.51  tff(c_1241, plain, (![A_118, B_119]: (k3_xboole_0(A_118, k1_relat_1(B_119))=k1_relat_1(k7_relat_1(B_119, A_118)) | ~v1_relat_1(B_119))), inference(superposition, [status(thm), theory('equality')], [c_2, c_929])).
% 3.15/1.51  tff(c_810, plain, (![A_78, B_79]: (r1_xboole_0(A_78, B_79) | k3_xboole_0(A_78, B_79)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.15/1.51  tff(c_762, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 3.15/1.51  tff(c_813, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_810, c_762])).
% 3.15/1.51  tff(c_821, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_813])).
% 3.15/1.51  tff(c_1263, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1241, c_821])).
% 3.15/1.51  tff(c_1305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_763, c_1263])).
% 3.15/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.51  
% 3.15/1.51  Inference rules
% 3.15/1.51  ----------------------
% 3.15/1.51  #Ref     : 0
% 3.15/1.51  #Sup     : 298
% 3.15/1.51  #Fact    : 0
% 3.15/1.51  #Define  : 0
% 3.15/1.51  #Split   : 3
% 3.15/1.51  #Chain   : 0
% 3.15/1.51  #Close   : 0
% 3.15/1.51  
% 3.15/1.51  Ordering : KBO
% 3.15/1.51  
% 3.15/1.51  Simplification rules
% 3.15/1.51  ----------------------
% 3.15/1.51  #Subsume      : 18
% 3.15/1.51  #Demod        : 141
% 3.15/1.51  #Tautology    : 168
% 3.15/1.51  #SimpNegUnit  : 3
% 3.15/1.51  #BackRed      : 0
% 3.15/1.51  
% 3.15/1.51  #Partial instantiations: 0
% 3.15/1.51  #Strategies tried      : 1
% 3.15/1.51  
% 3.15/1.51  Timing (in seconds)
% 3.15/1.51  ----------------------
% 3.15/1.51  Preprocessing        : 0.32
% 3.15/1.51  Parsing              : 0.17
% 3.15/1.51  CNF conversion       : 0.02
% 3.15/1.51  Main loop            : 0.42
% 3.15/1.51  Inferencing          : 0.15
% 3.15/1.51  Reduction            : 0.14
% 3.15/1.51  Demodulation         : 0.10
% 3.15/1.51  BG Simplification    : 0.02
% 3.15/1.52  Subsumption          : 0.08
% 3.15/1.52  Abstraction          : 0.02
% 3.15/1.52  MUC search           : 0.00
% 3.15/1.52  Cooper               : 0.00
% 3.15/1.52  Total                : 0.77
% 3.15/1.52  Index Insertion      : 0.00
% 3.15/1.52  Index Deletion       : 0.00
% 3.15/1.52  Index Matching       : 0.00
% 3.15/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
