%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:24 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   50 (  55 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 (  90 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k5_xboole_0(B,C))
    <=> ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(c_42,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | k4_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_30])).

tff(c_16,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_67,plain,(
    ! [A_6,B_7] : k4_xboole_0(k3_xboole_0(A_6,B_7),A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_48])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_446,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(A_67,B_66)
      | ~ v1_zfmisc_1(B_66)
      | v1_xboole_0(B_66)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1059,plain,(
    ! [B_115,A_116] :
      ( B_115 = A_116
      | ~ v1_zfmisc_1(B_115)
      | v1_xboole_0(B_115)
      | v1_xboole_0(A_116)
      | k4_xboole_0(A_116,B_115) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_446])).

tff(c_1061,plain,(
    ! [A_116] :
      ( A_116 = '#skF_1'
      | v1_xboole_0('#skF_1')
      | v1_xboole_0(A_116)
      | k4_xboole_0(A_116,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_1059])).

tff(c_1065,plain,(
    ! [A_117] :
      ( A_117 = '#skF_1'
      | v1_xboole_0(A_117)
      | k4_xboole_0(A_117,'#skF_1') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1061])).

tff(c_32,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1071,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1065,c_32])).

tff(c_1078,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_1071])).

tff(c_26,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),k5_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_313,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_xboole_0(A_51,k3_xboole_0(B_52,C_53))
      | ~ r1_tarski(A_51,k5_xboole_0(B_52,C_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( ~ r1_xboole_0(B_13,A_12)
      | ~ r1_tarski(B_13,A_12)
      | v1_xboole_0(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_964,plain,(
    ! [A_108,B_109,C_110] :
      ( ~ r1_tarski(A_108,k3_xboole_0(B_109,C_110))
      | v1_xboole_0(A_108)
      | ~ r1_tarski(A_108,k5_xboole_0(B_109,C_110)) ) ),
    inference(resolution,[status(thm)],[c_313,c_22])).

tff(c_991,plain,(
    ! [A_15,B_16] :
      ( ~ r1_tarski(k4_xboole_0(A_15,B_16),k3_xboole_0(A_15,B_16))
      | v1_xboole_0(k4_xboole_0(A_15,B_16)) ) ),
    inference(resolution,[status(thm)],[c_26,c_964])).

tff(c_1090,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | v1_xboole_0(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1078,c_991])).

tff(c_1112,plain,(
    v1_xboole_0(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1090])).

tff(c_24,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1122,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1112,c_24])).

tff(c_1126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:34:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.46  
% 2.96/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.47  %$ r1_xboole_0 > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.25/1.47  
% 3.25/1.47  %Foreground sorts:
% 3.25/1.47  
% 3.25/1.47  
% 3.25/1.47  %Background operators:
% 3.25/1.47  
% 3.25/1.47  
% 3.25/1.47  %Foreground operators:
% 3.25/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.25/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.25/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.25/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.47  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.25/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.25/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.25/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.25/1.47  
% 3.25/1.48  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 3.25/1.48  tff(f_84, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 3.25/1.48  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.25/1.48  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.25/1.48  tff(f_72, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.25/1.48  tff(f_59, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_xboole_1)).
% 3.25/1.48  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k5_xboole_0(B, C)) <=> (r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, k3_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 3.25/1.48  tff(f_53, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.25/1.48  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 3.25/1.48  tff(c_42, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | k4_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.25/1.48  tff(c_30, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.25/1.48  tff(c_46, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_30])).
% 3.25/1.48  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.25/1.48  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.25/1.48  tff(c_48, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.25/1.48  tff(c_67, plain, (![A_6, B_7]: (k4_xboole_0(k3_xboole_0(A_6, B_7), A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_48])).
% 3.25/1.48  tff(c_36, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.25/1.48  tff(c_34, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.25/1.48  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.25/1.48  tff(c_446, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(A_67, B_66) | ~v1_zfmisc_1(B_66) | v1_xboole_0(B_66) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.25/1.48  tff(c_1059, plain, (![B_115, A_116]: (B_115=A_116 | ~v1_zfmisc_1(B_115) | v1_xboole_0(B_115) | v1_xboole_0(A_116) | k4_xboole_0(A_116, B_115)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_446])).
% 3.25/1.48  tff(c_1061, plain, (![A_116]: (A_116='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(A_116) | k4_xboole_0(A_116, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_1059])).
% 3.25/1.48  tff(c_1065, plain, (![A_117]: (A_117='#skF_1' | v1_xboole_0(A_117) | k4_xboole_0(A_117, '#skF_1')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_36, c_1061])).
% 3.25/1.48  tff(c_32, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.25/1.48  tff(c_1071, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1065, c_32])).
% 3.25/1.48  tff(c_1078, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_1071])).
% 3.25/1.48  tff(c_26, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), k5_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.25/1.48  tff(c_313, plain, (![A_51, B_52, C_53]: (r1_xboole_0(A_51, k3_xboole_0(B_52, C_53)) | ~r1_tarski(A_51, k5_xboole_0(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.25/1.48  tff(c_22, plain, (![B_13, A_12]: (~r1_xboole_0(B_13, A_12) | ~r1_tarski(B_13, A_12) | v1_xboole_0(B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.25/1.48  tff(c_964, plain, (![A_108, B_109, C_110]: (~r1_tarski(A_108, k3_xboole_0(B_109, C_110)) | v1_xboole_0(A_108) | ~r1_tarski(A_108, k5_xboole_0(B_109, C_110)))), inference(resolution, [status(thm)], [c_313, c_22])).
% 3.25/1.48  tff(c_991, plain, (![A_15, B_16]: (~r1_tarski(k4_xboole_0(A_15, B_16), k3_xboole_0(A_15, B_16)) | v1_xboole_0(k4_xboole_0(A_15, B_16)))), inference(resolution, [status(thm)], [c_26, c_964])).
% 3.25/1.48  tff(c_1090, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1') | v1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1078, c_991])).
% 3.25/1.48  tff(c_1112, plain, (v1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1090])).
% 3.25/1.48  tff(c_24, plain, (![A_14]: (k1_xboole_0=A_14 | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.25/1.48  tff(c_1122, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1112, c_24])).
% 3.25/1.48  tff(c_1126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1122])).
% 3.25/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.48  
% 3.25/1.48  Inference rules
% 3.25/1.48  ----------------------
% 3.25/1.48  #Ref     : 0
% 3.25/1.48  #Sup     : 248
% 3.25/1.48  #Fact    : 0
% 3.25/1.48  #Define  : 0
% 3.25/1.48  #Split   : 0
% 3.25/1.48  #Chain   : 0
% 3.25/1.48  #Close   : 0
% 3.25/1.48  
% 3.25/1.48  Ordering : KBO
% 3.25/1.48  
% 3.25/1.48  Simplification rules
% 3.25/1.48  ----------------------
% 3.25/1.48  #Subsume      : 25
% 3.25/1.48  #Demod        : 171
% 3.25/1.48  #Tautology    : 144
% 3.25/1.48  #SimpNegUnit  : 2
% 3.25/1.48  #BackRed      : 1
% 3.25/1.48  
% 3.25/1.48  #Partial instantiations: 0
% 3.25/1.48  #Strategies tried      : 1
% 3.25/1.48  
% 3.25/1.48  Timing (in seconds)
% 3.25/1.48  ----------------------
% 3.32/1.48  Preprocessing        : 0.29
% 3.32/1.48  Parsing              : 0.16
% 3.32/1.48  CNF conversion       : 0.02
% 3.32/1.48  Main loop            : 0.43
% 3.32/1.48  Inferencing          : 0.17
% 3.32/1.48  Reduction            : 0.14
% 3.32/1.48  Demodulation         : 0.10
% 3.32/1.48  BG Simplification    : 0.02
% 3.32/1.48  Subsumption          : 0.08
% 3.32/1.48  Abstraction          : 0.02
% 3.32/1.48  MUC search           : 0.00
% 3.32/1.48  Cooper               : 0.00
% 3.32/1.48  Total                : 0.75
% 3.32/1.48  Index Insertion      : 0.00
% 3.32/1.48  Index Deletion       : 0.00
% 3.32/1.48  Index Matching       : 0.00
% 3.32/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
