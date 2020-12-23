%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:59 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 100 expanded)
%              Number of leaves         :   27 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :   99 ( 271 expanded)
%              Number of equality atoms :   47 ( 124 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_1 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_67,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_79,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    ! [A_17,B_18] : v1_funct_1('#skF_6'(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34,plain,(
    ! [A_17,B_18] : k1_relat_1('#skF_6'(A_17,B_18)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ! [A_17,B_18] : v1_relat_1('#skF_6'(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_44,plain,(
    ! [A_24] : v1_funct_1('#skF_7'(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,(
    ! [A_24] : k1_relat_1('#skF_7'(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    ! [A_24] : v1_relat_1('#skF_7'(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_69,plain,(
    ! [C_44,B_45] :
      ( C_44 = B_45
      | k1_relat_1(C_44) != '#skF_8'
      | k1_relat_1(B_45) != '#skF_8'
      | ~ v1_funct_1(C_44)
      | ~ v1_relat_1(C_44)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_75,plain,(
    ! [B_45,A_24] :
      ( B_45 = '#skF_7'(A_24)
      | k1_relat_1('#skF_7'(A_24)) != '#skF_8'
      | k1_relat_1(B_45) != '#skF_8'
      | ~ v1_funct_1('#skF_7'(A_24))
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_46,c_69])).

tff(c_254,plain,(
    ! [B_72,A_73] :
      ( B_72 = '#skF_7'(A_73)
      | A_73 != '#skF_8'
      | k1_relat_1(B_72) != '#skF_8'
      | ~ v1_funct_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_75])).

tff(c_258,plain,(
    ! [A_73,A_17,B_18] :
      ( '#skF_7'(A_73) = '#skF_6'(A_17,B_18)
      | A_73 != '#skF_8'
      | k1_relat_1('#skF_6'(A_17,B_18)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_17,B_18)) ) ),
    inference(resolution,[status(thm)],[c_38,c_254])).

tff(c_342,plain,(
    ! [A_81,A_82,B_83] :
      ( '#skF_7'(A_81) = '#skF_6'(A_82,B_83)
      | A_81 != '#skF_8'
      | A_82 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_258])).

tff(c_32,plain,(
    ! [A_17,B_18,D_23] :
      ( k1_funct_1('#skF_6'(A_17,B_18),D_23) = B_18
      | ~ r2_hidden(D_23,A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_477,plain,(
    ! [A_100,D_101,B_102,A_103] :
      ( k1_funct_1('#skF_7'(A_100),D_101) = B_102
      | ~ r2_hidden(D_101,A_103)
      | A_100 != '#skF_8'
      | A_103 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_32])).

tff(c_714,plain,(
    ! [A_112,A_113] :
      ( k1_funct_1('#skF_7'(A_112),'#skF_1'(A_113)) = '#skF_8'
      | A_112 != '#skF_8'
      | A_113 != '#skF_8'
      | v1_xboole_0(A_113) ) ),
    inference(resolution,[status(thm)],[c_4,c_477])).

tff(c_40,plain,(
    ! [A_24,C_29] :
      ( k1_funct_1('#skF_7'(A_24),C_29) = k1_xboole_0
      | ~ r2_hidden(C_29,A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_717,plain,(
    ! [A_113,A_112] :
      ( k1_xboole_0 = '#skF_8'
      | ~ r2_hidden('#skF_1'(A_113),A_112)
      | A_112 != '#skF_8'
      | A_113 != '#skF_8'
      | v1_xboole_0(A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_40])).

tff(c_874,plain,(
    ! [A_965,A_966] :
      ( ~ r2_hidden('#skF_1'(A_965),A_966)
      | A_966 != '#skF_8'
      | A_965 != '#skF_8'
      | v1_xboole_0(A_965) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_717])).

tff(c_907,plain,(
    ! [A_1014] :
      ( A_1014 != '#skF_8'
      | v1_xboole_0(A_1014) ) ),
    inference(resolution,[status(thm)],[c_4,c_874])).

tff(c_28,plain,(
    ! [A_13] :
      ( v1_relat_1(A_13)
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_919,plain,(
    ! [A_1014] :
      ( v1_relat_1(A_1014)
      | A_1014 != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_907,c_28])).

tff(c_235,plain,(
    ! [A_70] :
      ( k1_xboole_0 = A_70
      | r2_hidden(k4_tarski('#skF_4'(A_70),'#skF_5'(A_70)),A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_244,plain,(
    ! [A_70] :
      ( ~ v1_xboole_0(A_70)
      | k1_xboole_0 = A_70
      | ~ v1_relat_1(A_70) ) ),
    inference(resolution,[status(thm)],[c_235,c_2])).

tff(c_943,plain,(
    ! [A_1020] :
      ( k1_xboole_0 = A_1020
      | ~ v1_relat_1(A_1020)
      | A_1020 != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_907,c_244])).

tff(c_960,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_919,c_943])).

tff(c_972,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_960,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.49  
% 3.08/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.49  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_1 > #skF_2 > #skF_8 > #skF_3
% 3.08/1.49  
% 3.08/1.49  %Foreground sorts:
% 3.08/1.49  
% 3.08/1.49  
% 3.08/1.49  %Background operators:
% 3.08/1.49  
% 3.08/1.49  
% 3.08/1.49  %Foreground operators:
% 3.08/1.49  tff('#skF_7', type, '#skF_7': $i > $i).
% 3.08/1.49  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.08/1.49  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.08/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.08/1.49  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.08/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.08/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.08/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.08/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.08/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.08/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.08/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.08/1.49  tff('#skF_8', type, '#skF_8': $i).
% 3.08/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.08/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.08/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.08/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.08/1.49  
% 3.08/1.50  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.08/1.50  tff(f_98, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 3.08/1.50  tff(f_67, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 3.08/1.50  tff(f_79, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 3.08/1.50  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.08/1.50  tff(f_55, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 3.08/1.50  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.08/1.50  tff(c_48, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.08/1.50  tff(c_36, plain, (![A_17, B_18]: (v1_funct_1('#skF_6'(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.08/1.50  tff(c_34, plain, (![A_17, B_18]: (k1_relat_1('#skF_6'(A_17, B_18))=A_17)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.08/1.50  tff(c_38, plain, (![A_17, B_18]: (v1_relat_1('#skF_6'(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.08/1.50  tff(c_44, plain, (![A_24]: (v1_funct_1('#skF_7'(A_24)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.08/1.50  tff(c_42, plain, (![A_24]: (k1_relat_1('#skF_7'(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.08/1.50  tff(c_46, plain, (![A_24]: (v1_relat_1('#skF_7'(A_24)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.08/1.50  tff(c_69, plain, (![C_44, B_45]: (C_44=B_45 | k1_relat_1(C_44)!='#skF_8' | k1_relat_1(B_45)!='#skF_8' | ~v1_funct_1(C_44) | ~v1_relat_1(C_44) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.08/1.50  tff(c_75, plain, (![B_45, A_24]: (B_45='#skF_7'(A_24) | k1_relat_1('#skF_7'(A_24))!='#skF_8' | k1_relat_1(B_45)!='#skF_8' | ~v1_funct_1('#skF_7'(A_24)) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_46, c_69])).
% 3.08/1.50  tff(c_254, plain, (![B_72, A_73]: (B_72='#skF_7'(A_73) | A_73!='#skF_8' | k1_relat_1(B_72)!='#skF_8' | ~v1_funct_1(B_72) | ~v1_relat_1(B_72))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_75])).
% 3.08/1.50  tff(c_258, plain, (![A_73, A_17, B_18]: ('#skF_7'(A_73)='#skF_6'(A_17, B_18) | A_73!='#skF_8' | k1_relat_1('#skF_6'(A_17, B_18))!='#skF_8' | ~v1_funct_1('#skF_6'(A_17, B_18)))), inference(resolution, [status(thm)], [c_38, c_254])).
% 3.08/1.50  tff(c_342, plain, (![A_81, A_82, B_83]: ('#skF_7'(A_81)='#skF_6'(A_82, B_83) | A_81!='#skF_8' | A_82!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_258])).
% 3.08/1.50  tff(c_32, plain, (![A_17, B_18, D_23]: (k1_funct_1('#skF_6'(A_17, B_18), D_23)=B_18 | ~r2_hidden(D_23, A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.08/1.50  tff(c_477, plain, (![A_100, D_101, B_102, A_103]: (k1_funct_1('#skF_7'(A_100), D_101)=B_102 | ~r2_hidden(D_101, A_103) | A_100!='#skF_8' | A_103!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_342, c_32])).
% 3.08/1.50  tff(c_714, plain, (![A_112, A_113]: (k1_funct_1('#skF_7'(A_112), '#skF_1'(A_113))='#skF_8' | A_112!='#skF_8' | A_113!='#skF_8' | v1_xboole_0(A_113))), inference(resolution, [status(thm)], [c_4, c_477])).
% 3.08/1.50  tff(c_40, plain, (![A_24, C_29]: (k1_funct_1('#skF_7'(A_24), C_29)=k1_xboole_0 | ~r2_hidden(C_29, A_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.08/1.50  tff(c_717, plain, (![A_113, A_112]: (k1_xboole_0='#skF_8' | ~r2_hidden('#skF_1'(A_113), A_112) | A_112!='#skF_8' | A_113!='#skF_8' | v1_xboole_0(A_113))), inference(superposition, [status(thm), theory('equality')], [c_714, c_40])).
% 3.08/1.50  tff(c_874, plain, (![A_965, A_966]: (~r2_hidden('#skF_1'(A_965), A_966) | A_966!='#skF_8' | A_965!='#skF_8' | v1_xboole_0(A_965))), inference(negUnitSimplification, [status(thm)], [c_48, c_717])).
% 3.08/1.50  tff(c_907, plain, (![A_1014]: (A_1014!='#skF_8' | v1_xboole_0(A_1014))), inference(resolution, [status(thm)], [c_4, c_874])).
% 3.08/1.50  tff(c_28, plain, (![A_13]: (v1_relat_1(A_13) | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.08/1.50  tff(c_919, plain, (![A_1014]: (v1_relat_1(A_1014) | A_1014!='#skF_8')), inference(resolution, [status(thm)], [c_907, c_28])).
% 3.08/1.50  tff(c_235, plain, (![A_70]: (k1_xboole_0=A_70 | r2_hidden(k4_tarski('#skF_4'(A_70), '#skF_5'(A_70)), A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.08/1.50  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.08/1.50  tff(c_244, plain, (![A_70]: (~v1_xboole_0(A_70) | k1_xboole_0=A_70 | ~v1_relat_1(A_70))), inference(resolution, [status(thm)], [c_235, c_2])).
% 3.08/1.50  tff(c_943, plain, (![A_1020]: (k1_xboole_0=A_1020 | ~v1_relat_1(A_1020) | A_1020!='#skF_8')), inference(resolution, [status(thm)], [c_907, c_244])).
% 3.08/1.50  tff(c_960, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_919, c_943])).
% 3.08/1.50  tff(c_972, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_960, c_48])).
% 3.08/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.50  
% 3.08/1.50  Inference rules
% 3.08/1.50  ----------------------
% 3.08/1.50  #Ref     : 1
% 3.08/1.50  #Sup     : 215
% 3.08/1.50  #Fact    : 2
% 3.08/1.50  #Define  : 0
% 3.08/1.50  #Split   : 1
% 3.08/1.50  #Chain   : 0
% 3.08/1.50  #Close   : 0
% 3.08/1.50  
% 3.08/1.50  Ordering : KBO
% 3.08/1.50  
% 3.08/1.50  Simplification rules
% 3.08/1.50  ----------------------
% 3.08/1.50  #Subsume      : 71
% 3.08/1.50  #Demod        : 49
% 3.08/1.50  #Tautology    : 43
% 3.08/1.50  #SimpNegUnit  : 11
% 3.08/1.50  #BackRed      : 7
% 3.08/1.50  
% 3.08/1.50  #Partial instantiations: 546
% 3.08/1.50  #Strategies tried      : 1
% 3.08/1.50  
% 3.08/1.50  Timing (in seconds)
% 3.08/1.50  ----------------------
% 3.08/1.50  Preprocessing        : 0.31
% 3.08/1.50  Parsing              : 0.17
% 3.08/1.50  CNF conversion       : 0.02
% 3.08/1.50  Main loop            : 0.37
% 3.08/1.50  Inferencing          : 0.15
% 3.08/1.50  Reduction            : 0.10
% 3.08/1.50  Demodulation         : 0.07
% 3.08/1.50  BG Simplification    : 0.02
% 3.08/1.50  Subsumption          : 0.08
% 3.08/1.51  Abstraction          : 0.02
% 3.08/1.51  MUC search           : 0.00
% 3.08/1.51  Cooper               : 0.00
% 3.08/1.51  Total                : 0.71
% 3.08/1.51  Index Insertion      : 0.00
% 3.08/1.51  Index Deletion       : 0.00
% 3.08/1.51  Index Matching       : 0.00
% 3.08/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
