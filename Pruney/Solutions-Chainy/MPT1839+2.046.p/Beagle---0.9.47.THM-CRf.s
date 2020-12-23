%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:27 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   48 (  54 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 (  74 expanded)
%              Number of equality atoms :   28 (  31 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_84,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | k4_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_92,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_20])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_102,plain,(
    ! [A_37,B_38] : k5_xboole_0(A_37,k3_xboole_0(A_37,B_38)) = k4_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k5_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_102])).

tff(c_114,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_111])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_65,plain,(
    ! [A_5,B_6] : k4_xboole_0(k3_xboole_0(A_5,B_6),A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_57])).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_122,plain,(
    ! [B_40,A_41] :
      ( B_40 = A_41
      | ~ r1_tarski(A_41,B_40)
      | ~ v1_zfmisc_1(B_40)
      | v1_xboole_0(B_40)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_136,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ v1_zfmisc_1(B_42)
      | v1_xboole_0(B_42)
      | v1_xboole_0(A_43)
      | k4_xboole_0(A_43,B_42) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_122])).

tff(c_138,plain,(
    ! [A_43] :
      ( A_43 = '#skF_1'
      | v1_xboole_0('#skF_1')
      | v1_xboole_0(A_43)
      | k4_xboole_0(A_43,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_136])).

tff(c_142,plain,(
    ! [A_44] :
      ( A_44 = '#skF_1'
      | v1_xboole_0(A_44)
      | k4_xboole_0(A_44,'#skF_1') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_138])).

tff(c_22,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_145,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_142,c_22])).

tff(c_151,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_145])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_6])).

tff(c_169,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_160])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:45:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.26  
% 1.93/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.26  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.93/1.26  
% 1.93/1.26  %Foreground sorts:
% 1.93/1.26  
% 1.93/1.26  
% 1.93/1.26  %Background operators:
% 1.93/1.26  
% 1.93/1.26  
% 1.93/1.26  %Foreground operators:
% 1.93/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.93/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.26  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.93/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.93/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.93/1.26  
% 1.93/1.28  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.93/1.28  tff(f_66, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 1.93/1.28  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.93/1.28  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.93/1.28  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.93/1.28  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.93/1.28  tff(f_54, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 1.93/1.28  tff(c_84, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | k4_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.28  tff(c_20, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.93/1.28  tff(c_92, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_20])).
% 1.93/1.28  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.93/1.28  tff(c_10, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.28  tff(c_102, plain, (![A_37, B_38]: (k5_xboole_0(A_37, k3_xboole_0(A_37, B_38))=k4_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.28  tff(c_111, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k5_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_102])).
% 1.93/1.28  tff(c_114, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_111])).
% 1.93/1.28  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.28  tff(c_57, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.28  tff(c_65, plain, (![A_5, B_6]: (k4_xboole_0(k3_xboole_0(A_5, B_6), A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_57])).
% 1.93/1.28  tff(c_26, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.93/1.28  tff(c_24, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.93/1.28  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.28  tff(c_122, plain, (![B_40, A_41]: (B_40=A_41 | ~r1_tarski(A_41, B_40) | ~v1_zfmisc_1(B_40) | v1_xboole_0(B_40) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.93/1.28  tff(c_136, plain, (![B_42, A_43]: (B_42=A_43 | ~v1_zfmisc_1(B_42) | v1_xboole_0(B_42) | v1_xboole_0(A_43) | k4_xboole_0(A_43, B_42)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_122])).
% 1.93/1.28  tff(c_138, plain, (![A_43]: (A_43='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(A_43) | k4_xboole_0(A_43, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_136])).
% 1.93/1.28  tff(c_142, plain, (![A_44]: (A_44='#skF_1' | v1_xboole_0(A_44) | k4_xboole_0(A_44, '#skF_1')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_26, c_138])).
% 1.93/1.28  tff(c_22, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.93/1.28  tff(c_145, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_142, c_22])).
% 1.93/1.28  tff(c_151, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_65, c_145])).
% 1.93/1.28  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.28  tff(c_160, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_151, c_6])).
% 1.93/1.28  tff(c_169, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_114, c_160])).
% 1.93/1.28  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_169])).
% 1.93/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.28  
% 1.93/1.28  Inference rules
% 1.93/1.28  ----------------------
% 1.93/1.28  #Ref     : 0
% 1.93/1.28  #Sup     : 34
% 1.93/1.28  #Fact    : 0
% 1.93/1.28  #Define  : 0
% 1.93/1.28  #Split   : 0
% 1.93/1.28  #Chain   : 0
% 1.93/1.28  #Close   : 0
% 1.93/1.28  
% 1.93/1.28  Ordering : KBO
% 1.93/1.28  
% 1.93/1.28  Simplification rules
% 1.93/1.28  ----------------------
% 1.93/1.28  #Subsume      : 1
% 1.93/1.28  #Demod        : 6
% 1.93/1.28  #Tautology    : 21
% 1.93/1.28  #SimpNegUnit  : 2
% 1.93/1.28  #BackRed      : 1
% 1.93/1.28  
% 1.93/1.28  #Partial instantiations: 0
% 1.93/1.28  #Strategies tried      : 1
% 1.93/1.28  
% 1.93/1.28  Timing (in seconds)
% 1.93/1.28  ----------------------
% 1.93/1.28  Preprocessing        : 0.31
% 1.93/1.28  Parsing              : 0.17
% 1.93/1.28  CNF conversion       : 0.02
% 1.93/1.28  Main loop            : 0.14
% 1.93/1.28  Inferencing          : 0.06
% 1.93/1.28  Reduction            : 0.04
% 1.93/1.28  Demodulation         : 0.03
% 1.93/1.28  BG Simplification    : 0.01
% 1.93/1.28  Subsumption          : 0.02
% 1.93/1.28  Abstraction          : 0.01
% 1.93/1.28  MUC search           : 0.00
% 1.93/1.28  Cooper               : 0.00
% 1.93/1.28  Total                : 0.48
% 1.93/1.28  Index Insertion      : 0.00
% 1.93/1.28  Index Deletion       : 0.00
% 1.93/1.28  Index Matching       : 0.00
% 1.93/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
