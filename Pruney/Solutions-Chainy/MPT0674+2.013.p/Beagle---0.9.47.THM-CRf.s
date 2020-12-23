%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:24 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 (  94 expanded)
%              Number of equality atoms :   33 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r2_hidden(A,k1_relat_1(B))
         => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_58,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_62,plain,(
    ! [B_28,A_29] :
      ( k11_relat_1(B_28,A_29) != k1_xboole_0
      | ~ r2_hidden(A_29,k1_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_68,plain,
    ( k11_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_62])).

tff(c_72,plain,(
    k11_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_68])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),A_7)
      | k1_xboole_0 = A_7
      | k1_tarski(B_8) = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( r2_hidden(k4_tarski(A_10,B_11),C_12)
      | ~ r2_hidden(B_11,k11_relat_1(C_12,A_10))
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_95,plain,(
    ! [C_38,A_39,B_40] :
      ( k1_funct_1(C_38,A_39) = B_40
      | ~ r2_hidden(k4_tarski(A_39,B_40),C_38)
      | ~ v1_funct_1(C_38)
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_115,plain,(
    ! [C_44,A_45,B_46] :
      ( k1_funct_1(C_44,A_45) = B_46
      | ~ v1_funct_1(C_44)
      | ~ r2_hidden(B_46,k11_relat_1(C_44,A_45))
      | ~ v1_relat_1(C_44) ) ),
    inference(resolution,[status(thm)],[c_12,c_95])).

tff(c_305,plain,(
    ! [C_77,A_78,B_79] :
      ( '#skF_1'(k11_relat_1(C_77,A_78),B_79) = k1_funct_1(C_77,A_78)
      | ~ v1_funct_1(C_77)
      | ~ v1_relat_1(C_77)
      | k11_relat_1(C_77,A_78) = k1_xboole_0
      | k1_tarski(B_79) = k11_relat_1(C_77,A_78) ) ),
    inference(resolution,[status(thm)],[c_10,c_115])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( '#skF_1'(A_7,B_8) != B_8
      | k1_xboole_0 = A_7
      | k1_tarski(B_8) = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_313,plain,(
    ! [C_77,A_78,B_79] :
      ( k1_funct_1(C_77,A_78) != B_79
      | k11_relat_1(C_77,A_78) = k1_xboole_0
      | k1_tarski(B_79) = k11_relat_1(C_77,A_78)
      | ~ v1_funct_1(C_77)
      | ~ v1_relat_1(C_77)
      | k11_relat_1(C_77,A_78) = k1_xboole_0
      | k1_tarski(B_79) = k11_relat_1(C_77,A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_8])).

tff(c_695,plain,(
    ! [C_77,A_78] :
      ( k11_relat_1(C_77,A_78) = k1_xboole_0
      | k1_tarski(k1_funct_1(C_77,A_78)) = k11_relat_1(C_77,A_78)
      | ~ v1_funct_1(C_77)
      | ~ v1_relat_1(C_77)
      | k11_relat_1(C_77,A_78) = k1_xboole_0
      | k1_tarski(k1_funct_1(C_77,A_78)) = k11_relat_1(C_77,A_78) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_313])).

tff(c_726,plain,(
    ! [C_116,A_117] :
      ( ~ v1_funct_1(C_116)
      | ~ v1_relat_1(C_116)
      | k11_relat_1(C_116,A_117) = k1_xboole_0
      | k1_tarski(k1_funct_1(C_116,A_117)) = k11_relat_1(C_116,A_117) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_695])).

tff(c_26,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k11_relat_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_736,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k11_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_26])).

tff(c_745,plain,(
    k11_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_736])).

tff(c_747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_745])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.53  
% 3.20/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.54  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.20/1.54  
% 3.20/1.54  %Foreground sorts:
% 3.20/1.54  
% 3.20/1.54  
% 3.20/1.54  %Background operators:
% 3.20/1.54  
% 3.20/1.54  
% 3.20/1.54  %Foreground operators:
% 3.20/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.20/1.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.20/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.20/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.54  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.20/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.20/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.20/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.20/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.54  
% 3.20/1.55  tff(f_77, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 3.20/1.55  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.20/1.55  tff(f_45, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 3.20/1.55  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 3.20/1.55  tff(f_68, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 3.20/1.55  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.20/1.55  tff(c_28, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.20/1.55  tff(c_62, plain, (![B_28, A_29]: (k11_relat_1(B_28, A_29)!=k1_xboole_0 | ~r2_hidden(A_29, k1_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.20/1.55  tff(c_68, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_62])).
% 3.20/1.55  tff(c_72, plain, (k11_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_68])).
% 3.20/1.55  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.20/1.55  tff(c_10, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), A_7) | k1_xboole_0=A_7 | k1_tarski(B_8)=A_7)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.20/1.55  tff(c_12, plain, (![A_10, B_11, C_12]: (r2_hidden(k4_tarski(A_10, B_11), C_12) | ~r2_hidden(B_11, k11_relat_1(C_12, A_10)) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.20/1.55  tff(c_95, plain, (![C_38, A_39, B_40]: (k1_funct_1(C_38, A_39)=B_40 | ~r2_hidden(k4_tarski(A_39, B_40), C_38) | ~v1_funct_1(C_38) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.20/1.55  tff(c_115, plain, (![C_44, A_45, B_46]: (k1_funct_1(C_44, A_45)=B_46 | ~v1_funct_1(C_44) | ~r2_hidden(B_46, k11_relat_1(C_44, A_45)) | ~v1_relat_1(C_44))), inference(resolution, [status(thm)], [c_12, c_95])).
% 3.20/1.55  tff(c_305, plain, (![C_77, A_78, B_79]: ('#skF_1'(k11_relat_1(C_77, A_78), B_79)=k1_funct_1(C_77, A_78) | ~v1_funct_1(C_77) | ~v1_relat_1(C_77) | k11_relat_1(C_77, A_78)=k1_xboole_0 | k1_tarski(B_79)=k11_relat_1(C_77, A_78))), inference(resolution, [status(thm)], [c_10, c_115])).
% 3.20/1.55  tff(c_8, plain, (![A_7, B_8]: ('#skF_1'(A_7, B_8)!=B_8 | k1_xboole_0=A_7 | k1_tarski(B_8)=A_7)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.20/1.55  tff(c_313, plain, (![C_77, A_78, B_79]: (k1_funct_1(C_77, A_78)!=B_79 | k11_relat_1(C_77, A_78)=k1_xboole_0 | k1_tarski(B_79)=k11_relat_1(C_77, A_78) | ~v1_funct_1(C_77) | ~v1_relat_1(C_77) | k11_relat_1(C_77, A_78)=k1_xboole_0 | k1_tarski(B_79)=k11_relat_1(C_77, A_78))), inference(superposition, [status(thm), theory('equality')], [c_305, c_8])).
% 3.20/1.55  tff(c_695, plain, (![C_77, A_78]: (k11_relat_1(C_77, A_78)=k1_xboole_0 | k1_tarski(k1_funct_1(C_77, A_78))=k11_relat_1(C_77, A_78) | ~v1_funct_1(C_77) | ~v1_relat_1(C_77) | k11_relat_1(C_77, A_78)=k1_xboole_0 | k1_tarski(k1_funct_1(C_77, A_78))=k11_relat_1(C_77, A_78))), inference(reflexivity, [status(thm), theory('equality')], [c_313])).
% 3.20/1.55  tff(c_726, plain, (![C_116, A_117]: (~v1_funct_1(C_116) | ~v1_relat_1(C_116) | k11_relat_1(C_116, A_117)=k1_xboole_0 | k1_tarski(k1_funct_1(C_116, A_117))=k11_relat_1(C_116, A_117))), inference(factorization, [status(thm), theory('equality')], [c_695])).
% 3.20/1.55  tff(c_26, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k11_relat_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.20/1.55  tff(c_736, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_726, c_26])).
% 3.20/1.55  tff(c_745, plain, (k11_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_736])).
% 3.20/1.55  tff(c_747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_745])).
% 3.20/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.55  
% 3.20/1.55  Inference rules
% 3.20/1.55  ----------------------
% 3.20/1.55  #Ref     : 1
% 3.20/1.55  #Sup     : 163
% 3.20/1.55  #Fact    : 3
% 3.20/1.55  #Define  : 0
% 3.20/1.55  #Split   : 3
% 3.20/1.55  #Chain   : 0
% 3.20/1.55  #Close   : 0
% 3.20/1.55  
% 3.20/1.55  Ordering : KBO
% 3.20/1.55  
% 3.20/1.55  Simplification rules
% 3.20/1.55  ----------------------
% 3.20/1.55  #Subsume      : 42
% 3.20/1.55  #Demod        : 3
% 3.20/1.55  #Tautology    : 27
% 3.20/1.55  #SimpNegUnit  : 4
% 3.20/1.55  #BackRed      : 0
% 3.20/1.55  
% 3.20/1.55  #Partial instantiations: 0
% 3.20/1.55  #Strategies tried      : 1
% 3.20/1.55  
% 3.20/1.55  Timing (in seconds)
% 3.20/1.55  ----------------------
% 3.20/1.55  Preprocessing        : 0.30
% 3.20/1.55  Parsing              : 0.16
% 3.20/1.55  CNF conversion       : 0.02
% 3.20/1.55  Main loop            : 0.48
% 3.20/1.55  Inferencing          : 0.19
% 3.20/1.55  Reduction            : 0.11
% 3.20/1.55  Demodulation         : 0.07
% 3.20/1.55  BG Simplification    : 0.02
% 3.20/1.55  Subsumption          : 0.12
% 3.20/1.55  Abstraction          : 0.03
% 3.20/1.55  MUC search           : 0.00
% 3.20/1.55  Cooper               : 0.00
% 3.20/1.55  Total                : 0.81
% 3.20/1.55  Index Insertion      : 0.00
% 3.20/1.55  Index Deletion       : 0.00
% 3.20/1.55  Index Matching       : 0.00
% 3.20/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
