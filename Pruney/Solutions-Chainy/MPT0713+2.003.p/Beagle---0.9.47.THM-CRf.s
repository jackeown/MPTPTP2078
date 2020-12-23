%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:35 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   53 (  73 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   82 ( 137 expanded)
%              Number of equality atoms :   39 (  55 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r2_hidden(A,k1_relat_1(B))
         => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_96,plain,(
    ! [B_39,A_40] :
      ( k11_relat_1(B_39,A_40) != k1_xboole_0
      | ~ r2_hidden(A_40,k1_relat_1(B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_103,plain,
    ( k11_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_96])).

tff(c_107,plain,(
    k11_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_103])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),A_7)
      | k1_xboole_0 = A_7
      | k1_tarski(B_8) = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] :
      ( r2_hidden(k4_tarski(A_15,B_16),C_17)
      | ~ r2_hidden(B_16,k11_relat_1(C_17,A_15))
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_213,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_funct_1(A_60,B_61) = C_62
      | ~ r2_hidden(k4_tarski(B_61,C_62),A_60)
      | ~ r2_hidden(B_61,k1_relat_1(A_60))
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_261,plain,(
    ! [C_68,A_69,B_70] :
      ( k1_funct_1(C_68,A_69) = B_70
      | ~ r2_hidden(A_69,k1_relat_1(C_68))
      | ~ v1_funct_1(C_68)
      | ~ r2_hidden(B_70,k11_relat_1(C_68,A_69))
      | ~ v1_relat_1(C_68) ) ),
    inference(resolution,[status(thm)],[c_16,c_213])).

tff(c_276,plain,(
    ! [B_70] :
      ( k1_funct_1('#skF_3','#skF_2') = B_70
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden(B_70,k11_relat_1('#skF_3','#skF_2'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_261])).

tff(c_285,plain,(
    ! [B_71] :
      ( k1_funct_1('#skF_3','#skF_2') = B_71
      | ~ r2_hidden(B_71,k11_relat_1('#skF_3','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_276])).

tff(c_301,plain,(
    ! [B_8] :
      ( '#skF_1'(k11_relat_1('#skF_3','#skF_2'),B_8) = k1_funct_1('#skF_3','#skF_2')
      | k11_relat_1('#skF_3','#skF_2') = k1_xboole_0
      | k1_tarski(B_8) = k11_relat_1('#skF_3','#skF_2') ) ),
    inference(resolution,[status(thm)],[c_10,c_285])).

tff(c_311,plain,(
    ! [B_72] :
      ( '#skF_1'(k11_relat_1('#skF_3','#skF_2'),B_72) = k1_funct_1('#skF_3','#skF_2')
      | k1_tarski(B_72) = k11_relat_1('#skF_3','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_301])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( '#skF_1'(A_7,B_8) != B_8
      | k1_xboole_0 = A_7
      | k1_tarski(B_8) = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_319,plain,(
    ! [B_72] :
      ( k1_funct_1('#skF_3','#skF_2') != B_72
      | k11_relat_1('#skF_3','#skF_2') = k1_xboole_0
      | k1_tarski(B_72) = k11_relat_1('#skF_3','#skF_2')
      | k1_tarski(B_72) = k11_relat_1('#skF_3','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_8])).

tff(c_327,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) = k11_relat_1('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_319])).

tff(c_81,plain,(
    ! [A_35,B_36] :
      ( k9_relat_1(A_35,k1_tarski(B_36)) = k11_relat_1(A_35,B_36)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_58,plain,(
    ! [B_30,A_31] :
      ( k2_relat_1(k7_relat_1(B_30,A_31)) = k9_relat_1(B_30,A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_32,plain,(
    k2_relat_1(k7_relat_1('#skF_3',k1_tarski('#skF_2'))) != k1_tarski(k1_funct_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_64,plain,
    ( k9_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_tarski(k1_funct_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_32])).

tff(c_70,plain,(
    k9_relat_1('#skF_3',k1_tarski('#skF_2')) != k1_tarski(k1_funct_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_64])).

tff(c_87,plain,
    ( k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k11_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_70])).

tff(c_93,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k11_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_87])).

tff(c_332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.31  
% 2.25/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.31  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.25/1.31  
% 2.25/1.31  %Foreground sorts:
% 2.25/1.31  
% 2.25/1.31  
% 2.25/1.31  %Background operators:
% 2.25/1.31  
% 2.25/1.31  
% 2.25/1.31  %Foreground operators:
% 2.25/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.25/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.25/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.25/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.25/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.25/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.25/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.31  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.25/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.25/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.25/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.25/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.25/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.31  
% 2.53/1.33  tff(f_94, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_funct_1)).
% 2.53/1.33  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 2.53/1.33  tff(f_45, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 2.53/1.33  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 2.53/1.33  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 2.53/1.33  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 2.53/1.33  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.53/1.33  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.53/1.33  tff(c_34, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.53/1.33  tff(c_96, plain, (![B_39, A_40]: (k11_relat_1(B_39, A_40)!=k1_xboole_0 | ~r2_hidden(A_40, k1_relat_1(B_39)) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.53/1.33  tff(c_103, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_96])).
% 2.53/1.33  tff(c_107, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_103])).
% 2.53/1.33  tff(c_10, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), A_7) | k1_xboole_0=A_7 | k1_tarski(B_8)=A_7)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.53/1.33  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.53/1.33  tff(c_16, plain, (![A_15, B_16, C_17]: (r2_hidden(k4_tarski(A_15, B_16), C_17) | ~r2_hidden(B_16, k11_relat_1(C_17, A_15)) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.53/1.33  tff(c_213, plain, (![A_60, B_61, C_62]: (k1_funct_1(A_60, B_61)=C_62 | ~r2_hidden(k4_tarski(B_61, C_62), A_60) | ~r2_hidden(B_61, k1_relat_1(A_60)) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.53/1.33  tff(c_261, plain, (![C_68, A_69, B_70]: (k1_funct_1(C_68, A_69)=B_70 | ~r2_hidden(A_69, k1_relat_1(C_68)) | ~v1_funct_1(C_68) | ~r2_hidden(B_70, k11_relat_1(C_68, A_69)) | ~v1_relat_1(C_68))), inference(resolution, [status(thm)], [c_16, c_213])).
% 2.53/1.33  tff(c_276, plain, (![B_70]: (k1_funct_1('#skF_3', '#skF_2')=B_70 | ~v1_funct_1('#skF_3') | ~r2_hidden(B_70, k11_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_261])).
% 2.53/1.33  tff(c_285, plain, (![B_71]: (k1_funct_1('#skF_3', '#skF_2')=B_71 | ~r2_hidden(B_71, k11_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_276])).
% 2.53/1.33  tff(c_301, plain, (![B_8]: ('#skF_1'(k11_relat_1('#skF_3', '#skF_2'), B_8)=k1_funct_1('#skF_3', '#skF_2') | k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | k1_tarski(B_8)=k11_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_285])).
% 2.53/1.33  tff(c_311, plain, (![B_72]: ('#skF_1'(k11_relat_1('#skF_3', '#skF_2'), B_72)=k1_funct_1('#skF_3', '#skF_2') | k1_tarski(B_72)=k11_relat_1('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_107, c_301])).
% 2.53/1.33  tff(c_8, plain, (![A_7, B_8]: ('#skF_1'(A_7, B_8)!=B_8 | k1_xboole_0=A_7 | k1_tarski(B_8)=A_7)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.53/1.33  tff(c_319, plain, (![B_72]: (k1_funct_1('#skF_3', '#skF_2')!=B_72 | k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | k1_tarski(B_72)=k11_relat_1('#skF_3', '#skF_2') | k1_tarski(B_72)=k11_relat_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_8])).
% 2.53/1.33  tff(c_327, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))=k11_relat_1('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_107, c_319])).
% 2.53/1.33  tff(c_81, plain, (![A_35, B_36]: (k9_relat_1(A_35, k1_tarski(B_36))=k11_relat_1(A_35, B_36) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.53/1.33  tff(c_58, plain, (![B_30, A_31]: (k2_relat_1(k7_relat_1(B_30, A_31))=k9_relat_1(B_30, A_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.53/1.33  tff(c_32, plain, (k2_relat_1(k7_relat_1('#skF_3', k1_tarski('#skF_2')))!=k1_tarski(k1_funct_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.53/1.33  tff(c_64, plain, (k9_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_tarski(k1_funct_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_58, c_32])).
% 2.53/1.33  tff(c_70, plain, (k9_relat_1('#skF_3', k1_tarski('#skF_2'))!=k1_tarski(k1_funct_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_64])).
% 2.53/1.33  tff(c_87, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k11_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_81, c_70])).
% 2.53/1.33  tff(c_93, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k11_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_87])).
% 2.53/1.33  tff(c_332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_327, c_93])).
% 2.53/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.33  
% 2.53/1.33  Inference rules
% 2.53/1.33  ----------------------
% 2.53/1.33  #Ref     : 0
% 2.53/1.33  #Sup     : 58
% 2.53/1.33  #Fact    : 0
% 2.53/1.33  #Define  : 0
% 2.53/1.33  #Split   : 0
% 2.53/1.33  #Chain   : 0
% 2.53/1.33  #Close   : 0
% 2.53/1.33  
% 2.53/1.33  Ordering : KBO
% 2.53/1.33  
% 2.53/1.33  Simplification rules
% 2.53/1.33  ----------------------
% 2.53/1.33  #Subsume      : 6
% 2.53/1.33  #Demod        : 22
% 2.53/1.33  #Tautology    : 19
% 2.53/1.33  #SimpNegUnit  : 3
% 2.53/1.33  #BackRed      : 3
% 2.53/1.33  
% 2.53/1.33  #Partial instantiations: 0
% 2.53/1.33  #Strategies tried      : 1
% 2.53/1.33  
% 2.53/1.33  Timing (in seconds)
% 2.53/1.33  ----------------------
% 2.53/1.33  Preprocessing        : 0.33
% 2.53/1.33  Parsing              : 0.17
% 2.53/1.33  CNF conversion       : 0.02
% 2.53/1.33  Main loop            : 0.23
% 2.53/1.33  Inferencing          : 0.09
% 2.53/1.33  Reduction            : 0.07
% 2.53/1.33  Demodulation         : 0.05
% 2.53/1.33  BG Simplification    : 0.02
% 2.53/1.33  Subsumption          : 0.04
% 2.53/1.33  Abstraction          : 0.02
% 2.53/1.33  MUC search           : 0.00
% 2.53/1.33  Cooper               : 0.00
% 2.53/1.33  Total                : 0.59
% 2.53/1.33  Index Insertion      : 0.00
% 2.53/1.33  Index Deletion       : 0.00
% 2.53/1.33  Index Matching       : 0.00
% 2.53/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
