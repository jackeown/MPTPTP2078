%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:47 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   53 (  59 expanded)
%              Number of leaves         :   34 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 (  71 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_28,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_58,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_68,plain,(
    ! [A_69,C_70,B_71] :
      ( ~ r2_hidden(A_69,C_70)
      | ~ r1_xboole_0(k2_tarski(A_69,B_71),C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_73,plain,(
    ! [A_69] : ~ r2_hidden(A_69,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_68])).

tff(c_24,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_1'(A_32),A_32)
      | v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_74,plain,(
    ! [A_72] : ~ r2_hidden(A_72,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_68])).

tff(c_79,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_74])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_52,plain,(
    ! [A_62] :
      ( v1_funct_1(A_62)
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_56,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_145,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_4'(A_105,B_106),k1_relat_1(B_106))
      | v5_funct_1(B_106,A_105)
      | ~ v1_funct_1(B_106)
      | ~ v1_relat_1(B_106)
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_148,plain,(
    ! [A_105] :
      ( r2_hidden('#skF_4'(A_105,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_105)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_145])).

tff(c_150,plain,(
    ! [A_105] :
      ( r2_hidden('#skF_4'(A_105,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_105)
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_56,c_148])).

tff(c_152,plain,(
    ! [A_107] :
      ( v5_funct_1(k1_xboole_0,A_107)
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_150])).

tff(c_38,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_155,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_152,c_38])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:17:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.25  
% 2.02/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.26  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 2.02/1.26  
% 2.02/1.26  %Foreground sorts:
% 2.02/1.26  
% 2.02/1.26  
% 2.02/1.26  %Background operators:
% 2.02/1.26  
% 2.02/1.26  
% 2.02/1.26  %Foreground operators:
% 2.02/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.02/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.02/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.02/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.02/1.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.02/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.26  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.02/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.02/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.02/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.02/1.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.02/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.02/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.02/1.26  
% 2.02/1.27  tff(f_85, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 2.02/1.27  tff(f_28, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.02/1.27  tff(f_45, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.02/1.27  tff(f_55, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.02/1.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.02/1.27  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.02/1.27  tff(f_58, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.02/1.27  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.02/1.27  tff(c_42, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.02/1.27  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.02/1.27  tff(c_4, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.02/1.27  tff(c_68, plain, (![A_69, C_70, B_71]: (~r2_hidden(A_69, C_70) | ~r1_xboole_0(k2_tarski(A_69, B_71), C_70))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.02/1.27  tff(c_73, plain, (![A_69]: (~r2_hidden(A_69, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_68])).
% 2.02/1.27  tff(c_24, plain, (![A_32]: (r2_hidden('#skF_1'(A_32), A_32) | v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.02/1.27  tff(c_74, plain, (![A_72]: (~r2_hidden(A_72, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_68])).
% 2.02/1.27  tff(c_79, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_74])).
% 2.02/1.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.02/1.27  tff(c_52, plain, (![A_62]: (v1_funct_1(A_62) | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.27  tff(c_56, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_52])).
% 2.02/1.27  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.02/1.27  tff(c_145, plain, (![A_105, B_106]: (r2_hidden('#skF_4'(A_105, B_106), k1_relat_1(B_106)) | v5_funct_1(B_106, A_105) | ~v1_funct_1(B_106) | ~v1_relat_1(B_106) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.02/1.27  tff(c_148, plain, (![A_105]: (r2_hidden('#skF_4'(A_105, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_105) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(superposition, [status(thm), theory('equality')], [c_28, c_145])).
% 2.02/1.27  tff(c_150, plain, (![A_105]: (r2_hidden('#skF_4'(A_105, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_105) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_56, c_148])).
% 2.02/1.27  tff(c_152, plain, (![A_107]: (v5_funct_1(k1_xboole_0, A_107) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(negUnitSimplification, [status(thm)], [c_73, c_150])).
% 2.02/1.27  tff(c_38, plain, (~v5_funct_1(k1_xboole_0, '#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.02/1.27  tff(c_155, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_152, c_38])).
% 2.02/1.27  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_155])).
% 2.02/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.27  
% 2.02/1.27  Inference rules
% 2.02/1.27  ----------------------
% 2.02/1.27  #Ref     : 1
% 2.02/1.27  #Sup     : 25
% 2.02/1.27  #Fact    : 0
% 2.02/1.27  #Define  : 0
% 2.02/1.27  #Split   : 0
% 2.02/1.27  #Chain   : 0
% 2.02/1.27  #Close   : 0
% 2.02/1.27  
% 2.02/1.27  Ordering : KBO
% 2.02/1.27  
% 2.02/1.27  Simplification rules
% 2.02/1.27  ----------------------
% 2.02/1.27  #Subsume      : 0
% 2.02/1.27  #Demod        : 4
% 2.02/1.27  #Tautology    : 19
% 2.02/1.27  #SimpNegUnit  : 1
% 2.02/1.27  #BackRed      : 0
% 2.02/1.27  
% 2.02/1.27  #Partial instantiations: 0
% 2.02/1.27  #Strategies tried      : 1
% 2.02/1.27  
% 2.02/1.27  Timing (in seconds)
% 2.02/1.27  ----------------------
% 2.02/1.27  Preprocessing        : 0.33
% 2.02/1.27  Parsing              : 0.18
% 2.02/1.27  CNF conversion       : 0.02
% 2.02/1.27  Main loop            : 0.14
% 2.02/1.27  Inferencing          : 0.06
% 2.02/1.27  Reduction            : 0.04
% 2.02/1.27  Demodulation         : 0.03
% 2.02/1.27  BG Simplification    : 0.01
% 2.02/1.27  Subsumption          : 0.01
% 2.02/1.27  Abstraction          : 0.01
% 2.02/1.27  MUC search           : 0.00
% 2.02/1.27  Cooper               : 0.00
% 2.02/1.27  Total                : 0.49
% 2.02/1.27  Index Insertion      : 0.00
% 2.02/1.27  Index Deletion       : 0.00
% 2.02/1.27  Index Matching       : 0.00
% 2.02/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
