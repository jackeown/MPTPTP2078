%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:37 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 105 expanded)
%              Number of leaves         :   29 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   61 ( 140 expanded)
%              Number of equality atoms :   29 (  69 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_48,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_44,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_52,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    ! [C_18] : r2_hidden(C_18,k1_tarski(C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_67,plain,(
    ! [B_35,A_36] :
      ( ~ r2_hidden(B_35,A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [C_18] : ~ v1_xboole_0(k1_tarski(C_18)) ),
    inference(resolution,[status(thm)],[c_28,c_67])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_109,plain,(
    ! [C_44,A_45] :
      ( C_44 = A_45
      | ~ r2_hidden(C_44,k1_tarski(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_113,plain,(
    ! [A_45] :
      ( '#skF_1'(k1_tarski(A_45)) = A_45
      | v1_xboole_0(k1_tarski(A_45)) ) ),
    inference(resolution,[status(thm)],[c_4,c_109])).

tff(c_119,plain,(
    ! [A_45] : '#skF_1'(k1_tarski(A_45)) = A_45 ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_113])).

tff(c_54,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_241,plain,(
    ! [B_58,A_59] :
      ( k1_tarski(B_58) = A_59
      | k1_xboole_0 = A_59
      | ~ r1_tarski(A_59,k1_tarski(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_258,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_4')
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_241])).

tff(c_263,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_286,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_28])).

tff(c_20,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_83,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ r1_tarski(A_41,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_88,plain,(
    ! [B_11] : k3_xboole_0(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_83])).

tff(c_145,plain,(
    ! [A_49,B_50] : k5_xboole_0(A_49,k3_xboole_0(A_49,B_50)) = k4_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_157,plain,(
    ! [B_51] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_145])).

tff(c_154,plain,(
    ! [B_11] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_145])).

tff(c_175,plain,(
    ! [B_56,B_55] : k4_xboole_0(k1_xboole_0,B_56) = k4_xboole_0(k1_xboole_0,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_154])).

tff(c_22,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_191,plain,(
    ! [B_56] : k4_xboole_0(k1_xboole_0,B_56) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_22])).

tff(c_217,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_154])).

tff(c_322,plain,(
    ! [A_61,C_62,B_63] :
      ( ~ r2_hidden(A_61,C_62)
      | ~ r2_hidden(A_61,B_63)
      | ~ r2_hidden(A_61,k5_xboole_0(B_63,C_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_334,plain,(
    ! [A_64] :
      ( ~ r2_hidden(A_64,k1_xboole_0)
      | ~ r2_hidden(A_64,k1_xboole_0)
      | ~ r2_hidden(A_64,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_322])).

tff(c_336,plain,(
    ~ r2_hidden('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_286,c_334])).

tff(c_343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_336])).

tff(c_344,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_354,plain,(
    '#skF_1'(k1_tarski('#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_119])).

tff(c_374,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_354])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_374])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.22  
% 2.03/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.22  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.03/1.22  
% 2.03/1.22  %Foreground sorts:
% 2.03/1.22  
% 2.03/1.22  
% 2.03/1.22  %Background operators:
% 2.03/1.22  
% 2.03/1.22  
% 2.03/1.22  %Foreground operators:
% 2.03/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.03/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.03/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.03/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.03/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.22  tff('#skF_5', type, '#skF_5': $i).
% 2.03/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.03/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.03/1.22  
% 2.19/1.23  tff(f_74, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.19/1.23  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.19/1.23  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.19/1.23  tff(f_69, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.19/1.23  tff(f_42, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.19/1.23  tff(f_48, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.19/1.23  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.19/1.23  tff(f_44, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.19/1.23  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.19/1.23  tff(c_52, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.19/1.23  tff(c_28, plain, (![C_18]: (r2_hidden(C_18, k1_tarski(C_18)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.19/1.23  tff(c_67, plain, (![B_35, A_36]: (~r2_hidden(B_35, A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.23  tff(c_71, plain, (![C_18]: (~v1_xboole_0(k1_tarski(C_18)))), inference(resolution, [status(thm)], [c_28, c_67])).
% 2.19/1.23  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.23  tff(c_109, plain, (![C_44, A_45]: (C_44=A_45 | ~r2_hidden(C_44, k1_tarski(A_45)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.19/1.23  tff(c_113, plain, (![A_45]: ('#skF_1'(k1_tarski(A_45))=A_45 | v1_xboole_0(k1_tarski(A_45)))), inference(resolution, [status(thm)], [c_4, c_109])).
% 2.19/1.23  tff(c_119, plain, (![A_45]: ('#skF_1'(k1_tarski(A_45))=A_45)), inference(negUnitSimplification, [status(thm)], [c_71, c_113])).
% 2.19/1.23  tff(c_54, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.19/1.23  tff(c_241, plain, (![B_58, A_59]: (k1_tarski(B_58)=A_59 | k1_xboole_0=A_59 | ~r1_tarski(A_59, k1_tarski(B_58)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.19/1.23  tff(c_258, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4') | k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_241])).
% 2.19/1.23  tff(c_263, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_258])).
% 2.19/1.23  tff(c_286, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_263, c_28])).
% 2.19/1.23  tff(c_20, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.19/1.23  tff(c_83, plain, (![A_41]: (k1_xboole_0=A_41 | ~r1_tarski(A_41, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.19/1.23  tff(c_88, plain, (![B_11]: (k3_xboole_0(k1_xboole_0, B_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_83])).
% 2.19/1.23  tff(c_145, plain, (![A_49, B_50]: (k5_xboole_0(A_49, k3_xboole_0(A_49, B_50))=k4_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.19/1.23  tff(c_157, plain, (![B_51]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_51))), inference(superposition, [status(thm), theory('equality')], [c_88, c_145])).
% 2.19/1.23  tff(c_154, plain, (![B_11]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_11))), inference(superposition, [status(thm), theory('equality')], [c_88, c_145])).
% 2.19/1.23  tff(c_175, plain, (![B_56, B_55]: (k4_xboole_0(k1_xboole_0, B_56)=k4_xboole_0(k1_xboole_0, B_55))), inference(superposition, [status(thm), theory('equality')], [c_157, c_154])).
% 2.19/1.23  tff(c_22, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.19/1.23  tff(c_191, plain, (![B_56]: (k4_xboole_0(k1_xboole_0, B_56)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_175, c_22])).
% 2.19/1.23  tff(c_217, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_191, c_154])).
% 2.19/1.23  tff(c_322, plain, (![A_61, C_62, B_63]: (~r2_hidden(A_61, C_62) | ~r2_hidden(A_61, B_63) | ~r2_hidden(A_61, k5_xboole_0(B_63, C_62)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.19/1.23  tff(c_334, plain, (![A_64]: (~r2_hidden(A_64, k1_xboole_0) | ~r2_hidden(A_64, k1_xboole_0) | ~r2_hidden(A_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_217, c_322])).
% 2.19/1.23  tff(c_336, plain, (~r2_hidden('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_286, c_334])).
% 2.19/1.23  tff(c_343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_286, c_336])).
% 2.19/1.23  tff(c_344, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_258])).
% 2.19/1.23  tff(c_354, plain, ('#skF_1'(k1_tarski('#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_344, c_119])).
% 2.19/1.23  tff(c_374, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_354])).
% 2.19/1.23  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_374])).
% 2.19/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.23  
% 2.19/1.23  Inference rules
% 2.19/1.23  ----------------------
% 2.19/1.23  #Ref     : 0
% 2.19/1.23  #Sup     : 84
% 2.19/1.23  #Fact    : 0
% 2.19/1.23  #Define  : 0
% 2.19/1.23  #Split   : 1
% 2.19/1.23  #Chain   : 0
% 2.19/1.23  #Close   : 0
% 2.19/1.23  
% 2.19/1.23  Ordering : KBO
% 2.19/1.23  
% 2.19/1.23  Simplification rules
% 2.19/1.23  ----------------------
% 2.19/1.23  #Subsume      : 15
% 2.19/1.23  #Demod        : 23
% 2.19/1.23  #Tautology    : 48
% 2.19/1.23  #SimpNegUnit  : 5
% 2.19/1.23  #BackRed      : 3
% 2.19/1.23  
% 2.19/1.23  #Partial instantiations: 0
% 2.19/1.23  #Strategies tried      : 1
% 2.19/1.23  
% 2.19/1.23  Timing (in seconds)
% 2.19/1.23  ----------------------
% 2.19/1.24  Preprocessing        : 0.31
% 2.19/1.24  Parsing              : 0.16
% 2.19/1.24  CNF conversion       : 0.02
% 2.19/1.24  Main loop            : 0.18
% 2.19/1.24  Inferencing          : 0.06
% 2.19/1.24  Reduction            : 0.06
% 2.19/1.24  Demodulation         : 0.04
% 2.19/1.24  BG Simplification    : 0.01
% 2.19/1.24  Subsumption          : 0.03
% 2.19/1.24  Abstraction          : 0.01
% 2.19/1.24  MUC search           : 0.00
% 2.19/1.24  Cooper               : 0.00
% 2.19/1.24  Total                : 0.51
% 2.19/1.24  Index Insertion      : 0.00
% 2.19/1.24  Index Deletion       : 0.00
% 2.19/1.24  Index Matching       : 0.00
% 2.19/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
