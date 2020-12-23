%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:01 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   42 (  53 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :   83 ( 134 expanded)
%              Number of equality atoms :   43 (  64 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_78,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_59,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_6,B_7] : v1_funct_1('#skF_2'(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_6,B_7] : k1_relat_1('#skF_2'(A_6,B_7)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_6,B_7] : v1_relat_1('#skF_2'(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_13] : v1_funct_1('#skF_3'(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_13] : k1_relat_1('#skF_3'(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [A_13] : v1_relat_1('#skF_3'(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_51,plain,(
    ! [C_37,B_38] :
      ( C_37 = B_38
      | k1_relat_1(C_37) != '#skF_4'
      | k1_relat_1(B_38) != '#skF_4'
      | ~ v1_funct_1(C_37)
      | ~ v1_relat_1(C_37)
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_55,plain,(
    ! [B_38,A_13] :
      ( B_38 = '#skF_3'(A_13)
      | k1_relat_1('#skF_3'(A_13)) != '#skF_4'
      | k1_relat_1(B_38) != '#skF_4'
      | ~ v1_funct_1('#skF_3'(A_13))
      | ~ v1_funct_1(B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_22,c_51])).

tff(c_86,plain,(
    ! [B_45,A_46] :
      ( B_45 = '#skF_3'(A_46)
      | A_46 != '#skF_4'
      | k1_relat_1(B_45) != '#skF_4'
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_55])).

tff(c_88,plain,(
    ! [A_46,A_6,B_7] :
      ( '#skF_3'(A_46) = '#skF_2'(A_6,B_7)
      | A_46 != '#skF_4'
      | k1_relat_1('#skF_2'(A_6,B_7)) != '#skF_4'
      | ~ v1_funct_1('#skF_2'(A_6,B_7)) ) ),
    inference(resolution,[status(thm)],[c_14,c_86])).

tff(c_167,plain,(
    ! [A_54,A_55,B_56] :
      ( '#skF_3'(A_54) = '#skF_2'(A_55,B_56)
      | A_54 != '#skF_4'
      | A_55 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_88])).

tff(c_8,plain,(
    ! [A_6,B_7,D_12] :
      ( k1_funct_1('#skF_2'(A_6,B_7),D_12) = B_7
      | ~ r2_hidden(D_12,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_288,plain,(
    ! [A_64,D_65,B_66,A_67] :
      ( k1_funct_1('#skF_3'(A_64),D_65) = B_66
      | ~ r2_hidden(D_65,A_67)
      | A_64 != '#skF_4'
      | A_67 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_8])).

tff(c_439,plain,(
    ! [A_75,A_76] :
      ( k1_funct_1('#skF_3'(A_75),'#skF_1'(A_76)) = '#skF_4'
      | A_75 != '#skF_4'
      | A_76 != '#skF_4'
      | v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_4,c_288])).

tff(c_16,plain,(
    ! [A_13,C_18] :
      ( k1_funct_1('#skF_3'(A_13),C_18) = k1_xboole_0
      | ~ r2_hidden(C_18,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_442,plain,(
    ! [A_76,A_75] :
      ( k1_xboole_0 = '#skF_4'
      | ~ r2_hidden('#skF_1'(A_76),A_75)
      | A_75 != '#skF_4'
      | A_76 != '#skF_4'
      | v1_xboole_0(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_16])).

tff(c_519,plain,(
    ! [A_260,A_261] :
      ( ~ r2_hidden('#skF_1'(A_260),A_261)
      | A_261 != '#skF_4'
      | A_260 != '#skF_4'
      | v1_xboole_0(A_260) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_442])).

tff(c_527,plain,(
    ! [A_269] :
      ( A_269 != '#skF_4'
      | v1_xboole_0(A_269) ) ),
    inference(resolution,[status(thm)],[c_4,c_519])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_532,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_527,c_6])).

tff(c_537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:48:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.27  
% 2.28/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.27  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 2.28/1.27  
% 2.28/1.27  %Foreground sorts:
% 2.28/1.27  
% 2.28/1.27  
% 2.28/1.27  %Background operators:
% 2.28/1.27  
% 2.28/1.27  
% 2.28/1.27  %Foreground operators:
% 2.28/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.28/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.28/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.28/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.27  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.28/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.28/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.27  
% 2.28/1.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.28/1.28  tff(f_78, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 2.28/1.28  tff(f_47, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 2.28/1.28  tff(f_59, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.28/1.28  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.28/1.28  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.28  tff(c_24, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.28/1.28  tff(c_12, plain, (![A_6, B_7]: (v1_funct_1('#skF_2'(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.28/1.28  tff(c_10, plain, (![A_6, B_7]: (k1_relat_1('#skF_2'(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.28/1.28  tff(c_14, plain, (![A_6, B_7]: (v1_relat_1('#skF_2'(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.28/1.28  tff(c_20, plain, (![A_13]: (v1_funct_1('#skF_3'(A_13)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.28/1.28  tff(c_18, plain, (![A_13]: (k1_relat_1('#skF_3'(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.28/1.28  tff(c_22, plain, (![A_13]: (v1_relat_1('#skF_3'(A_13)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.28/1.28  tff(c_51, plain, (![C_37, B_38]: (C_37=B_38 | k1_relat_1(C_37)!='#skF_4' | k1_relat_1(B_38)!='#skF_4' | ~v1_funct_1(C_37) | ~v1_relat_1(C_37) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.28/1.28  tff(c_55, plain, (![B_38, A_13]: (B_38='#skF_3'(A_13) | k1_relat_1('#skF_3'(A_13))!='#skF_4' | k1_relat_1(B_38)!='#skF_4' | ~v1_funct_1('#skF_3'(A_13)) | ~v1_funct_1(B_38) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_22, c_51])).
% 2.28/1.28  tff(c_86, plain, (![B_45, A_46]: (B_45='#skF_3'(A_46) | A_46!='#skF_4' | k1_relat_1(B_45)!='#skF_4' | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_55])).
% 2.28/1.28  tff(c_88, plain, (![A_46, A_6, B_7]: ('#skF_3'(A_46)='#skF_2'(A_6, B_7) | A_46!='#skF_4' | k1_relat_1('#skF_2'(A_6, B_7))!='#skF_4' | ~v1_funct_1('#skF_2'(A_6, B_7)))), inference(resolution, [status(thm)], [c_14, c_86])).
% 2.28/1.28  tff(c_167, plain, (![A_54, A_55, B_56]: ('#skF_3'(A_54)='#skF_2'(A_55, B_56) | A_54!='#skF_4' | A_55!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_88])).
% 2.28/1.28  tff(c_8, plain, (![A_6, B_7, D_12]: (k1_funct_1('#skF_2'(A_6, B_7), D_12)=B_7 | ~r2_hidden(D_12, A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.28/1.28  tff(c_288, plain, (![A_64, D_65, B_66, A_67]: (k1_funct_1('#skF_3'(A_64), D_65)=B_66 | ~r2_hidden(D_65, A_67) | A_64!='#skF_4' | A_67!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_167, c_8])).
% 2.28/1.28  tff(c_439, plain, (![A_75, A_76]: (k1_funct_1('#skF_3'(A_75), '#skF_1'(A_76))='#skF_4' | A_75!='#skF_4' | A_76!='#skF_4' | v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_4, c_288])).
% 2.28/1.28  tff(c_16, plain, (![A_13, C_18]: (k1_funct_1('#skF_3'(A_13), C_18)=k1_xboole_0 | ~r2_hidden(C_18, A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.28/1.28  tff(c_442, plain, (![A_76, A_75]: (k1_xboole_0='#skF_4' | ~r2_hidden('#skF_1'(A_76), A_75) | A_75!='#skF_4' | A_76!='#skF_4' | v1_xboole_0(A_76))), inference(superposition, [status(thm), theory('equality')], [c_439, c_16])).
% 2.28/1.28  tff(c_519, plain, (![A_260, A_261]: (~r2_hidden('#skF_1'(A_260), A_261) | A_261!='#skF_4' | A_260!='#skF_4' | v1_xboole_0(A_260))), inference(negUnitSimplification, [status(thm)], [c_24, c_442])).
% 2.28/1.28  tff(c_527, plain, (![A_269]: (A_269!='#skF_4' | v1_xboole_0(A_269))), inference(resolution, [status(thm)], [c_4, c_519])).
% 2.28/1.28  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.28  tff(c_532, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_527, c_6])).
% 2.28/1.28  tff(c_537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_532, c_24])).
% 2.28/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.28  
% 2.28/1.28  Inference rules
% 2.28/1.28  ----------------------
% 2.28/1.28  #Ref     : 1
% 2.28/1.28  #Sup     : 130
% 2.28/1.28  #Fact    : 0
% 2.28/1.28  #Define  : 0
% 2.28/1.28  #Split   : 0
% 2.28/1.28  #Chain   : 0
% 2.28/1.28  #Close   : 0
% 2.28/1.28  
% 2.28/1.28  Ordering : KBO
% 2.28/1.28  
% 2.28/1.28  Simplification rules
% 2.28/1.28  ----------------------
% 2.28/1.28  #Subsume      : 54
% 2.28/1.28  #Demod        : 33
% 2.28/1.28  #Tautology    : 27
% 2.28/1.28  #SimpNegUnit  : 1
% 2.28/1.28  #BackRed      : 3
% 2.28/1.28  
% 2.28/1.28  #Partial instantiations: 168
% 2.28/1.28  #Strategies tried      : 1
% 2.28/1.28  
% 2.28/1.28  Timing (in seconds)
% 2.28/1.28  ----------------------
% 2.28/1.29  Preprocessing        : 0.27
% 2.28/1.29  Parsing              : 0.15
% 2.28/1.29  CNF conversion       : 0.02
% 2.28/1.29  Main loop            : 0.26
% 2.28/1.29  Inferencing          : 0.11
% 2.28/1.29  Reduction            : 0.07
% 2.28/1.29  Demodulation         : 0.05
% 2.28/1.29  BG Simplification    : 0.02
% 2.28/1.29  Subsumption          : 0.05
% 2.28/1.29  Abstraction          : 0.01
% 2.28/1.29  MUC search           : 0.00
% 2.28/1.29  Cooper               : 0.00
% 2.28/1.29  Total                : 0.56
% 2.28/1.29  Index Insertion      : 0.00
% 2.28/1.29  Index Deletion       : 0.00
% 2.28/1.29  Index Matching       : 0.00
% 2.28/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
