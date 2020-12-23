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
% DateTime   : Thu Dec  3 10:28:27 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   49 (  56 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  79 expanded)
%              Number of equality atoms :   27 (  30 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_61,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | k4_xboole_0(A_29,B_30) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_65,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61,c_24])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,(
    ! [A_24,B_25] : r1_tarski(k4_xboole_0(A_24,B_25),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    ! [A_6] : r1_tarski(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_47])).

tff(c_75,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_75])).

tff(c_113,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_265,plain,(
    ! [A_44,B_45] : r1_tarski(k3_xboole_0(A_44,B_45),A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_8])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_278,plain,(
    ! [A_44,B_45] : k4_xboole_0(k3_xboole_0(A_44,B_45),A_44) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_265,c_4])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_499,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(A_58,B_57)
      | ~ v1_zfmisc_1(B_57)
      | v1_xboole_0(B_57)
      | v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_655,plain,(
    ! [B_63,A_64] :
      ( B_63 = A_64
      | ~ v1_zfmisc_1(B_63)
      | v1_xboole_0(B_63)
      | v1_xboole_0(A_64)
      | k4_xboole_0(A_64,B_63) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_499])).

tff(c_657,plain,(
    ! [A_64] :
      ( A_64 = '#skF_1'
      | v1_xboole_0('#skF_1')
      | v1_xboole_0(A_64)
      | k4_xboole_0(A_64,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_655])).

tff(c_661,plain,(
    ! [A_65] :
      ( A_65 = '#skF_1'
      | v1_xboole_0(A_65)
      | k4_xboole_0(A_65,'#skF_1') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_657])).

tff(c_26,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_664,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_661,c_26])).

tff(c_670,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_664])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_691,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_12])).

tff(c_698,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_691])).

tff(c_700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_698])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.31  
% 2.43/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.32  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.43/1.32  
% 2.43/1.32  %Foreground sorts:
% 2.43/1.32  
% 2.43/1.32  
% 2.43/1.32  %Background operators:
% 2.43/1.32  
% 2.43/1.32  
% 2.43/1.32  %Foreground operators:
% 2.43/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.43/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.43/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.43/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.43/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.43/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.32  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.43/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.43/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.43/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.43/1.32  
% 2.43/1.33  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.43/1.33  tff(f_70, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 2.43/1.33  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.43/1.33  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.43/1.33  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.43/1.33  tff(f_58, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.43/1.33  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.43/1.33  tff(c_61, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | k4_xboole_0(A_29, B_30)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.43/1.33  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.43/1.33  tff(c_65, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_61, c_24])).
% 2.43/1.33  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.43/1.33  tff(c_47, plain, (![A_24, B_25]: (r1_tarski(k4_xboole_0(A_24, B_25), A_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.43/1.33  tff(c_50, plain, (![A_6]: (r1_tarski(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_10, c_47])).
% 2.43/1.33  tff(c_75, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.43/1.33  tff(c_86, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_75])).
% 2.43/1.33  tff(c_113, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.43/1.33  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.43/1.33  tff(c_265, plain, (![A_44, B_45]: (r1_tarski(k3_xboole_0(A_44, B_45), A_44))), inference(superposition, [status(thm), theory('equality')], [c_113, c_8])).
% 2.43/1.33  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.43/1.33  tff(c_278, plain, (![A_44, B_45]: (k4_xboole_0(k3_xboole_0(A_44, B_45), A_44)=k1_xboole_0)), inference(resolution, [status(thm)], [c_265, c_4])).
% 2.43/1.33  tff(c_30, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.43/1.33  tff(c_28, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.43/1.33  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.43/1.33  tff(c_499, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(A_58, B_57) | ~v1_zfmisc_1(B_57) | v1_xboole_0(B_57) | v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.43/1.33  tff(c_655, plain, (![B_63, A_64]: (B_63=A_64 | ~v1_zfmisc_1(B_63) | v1_xboole_0(B_63) | v1_xboole_0(A_64) | k4_xboole_0(A_64, B_63)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_499])).
% 2.43/1.33  tff(c_657, plain, (![A_64]: (A_64='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(A_64) | k4_xboole_0(A_64, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_655])).
% 2.43/1.33  tff(c_661, plain, (![A_65]: (A_65='#skF_1' | v1_xboole_0(A_65) | k4_xboole_0(A_65, '#skF_1')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_30, c_657])).
% 2.43/1.33  tff(c_26, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.43/1.33  tff(c_664, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_661, c_26])).
% 2.43/1.33  tff(c_670, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_278, c_664])).
% 2.43/1.33  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.43/1.33  tff(c_691, plain, (k4_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_670, c_12])).
% 2.43/1.33  tff(c_698, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_86, c_691])).
% 2.43/1.33  tff(c_700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_698])).
% 2.43/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.33  
% 2.43/1.33  Inference rules
% 2.43/1.33  ----------------------
% 2.43/1.33  #Ref     : 0
% 2.43/1.33  #Sup     : 157
% 2.43/1.33  #Fact    : 0
% 2.43/1.33  #Define  : 0
% 2.43/1.33  #Split   : 1
% 2.43/1.33  #Chain   : 0
% 2.43/1.33  #Close   : 0
% 2.43/1.33  
% 2.43/1.33  Ordering : KBO
% 2.43/1.33  
% 2.43/1.33  Simplification rules
% 2.43/1.33  ----------------------
% 2.43/1.33  #Subsume      : 1
% 2.43/1.33  #Demod        : 136
% 2.43/1.33  #Tautology    : 135
% 2.43/1.33  #SimpNegUnit  : 2
% 2.43/1.33  #BackRed      : 1
% 2.43/1.33  
% 2.43/1.33  #Partial instantiations: 0
% 2.43/1.33  #Strategies tried      : 1
% 2.43/1.33  
% 2.43/1.33  Timing (in seconds)
% 2.43/1.33  ----------------------
% 2.43/1.33  Preprocessing        : 0.30
% 2.43/1.33  Parsing              : 0.16
% 2.43/1.33  CNF conversion       : 0.02
% 2.43/1.33  Main loop            : 0.26
% 2.43/1.33  Inferencing          : 0.11
% 2.43/1.33  Reduction            : 0.09
% 2.43/1.33  Demodulation         : 0.07
% 2.43/1.33  BG Simplification    : 0.01
% 2.43/1.33  Subsumption          : 0.03
% 2.43/1.33  Abstraction          : 0.02
% 2.43/1.33  MUC search           : 0.00
% 2.43/1.33  Cooper               : 0.00
% 2.43/1.33  Total                : 0.59
% 2.43/1.33  Index Insertion      : 0.00
% 2.43/1.33  Index Deletion       : 0.00
% 2.43/1.33  Index Matching       : 0.00
% 2.43/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
