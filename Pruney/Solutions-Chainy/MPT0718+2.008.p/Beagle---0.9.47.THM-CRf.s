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
% DateTime   : Thu Dec  3 10:05:42 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   51 (  64 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   96 ( 167 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v2_relat_1,type,(
    v2_relat_1: $i > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v5_funct_1(A,B)
                & k1_relat_1(A) = k1_relat_1(B) )
             => v2_relat_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_relat_1(A)
      <=> ! [B] :
            ~ ( r2_hidden(B,k1_relat_1(A))
              & v1_xboole_0(k1_funct_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_funct_1)).

tff(f_47,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_75,axiom,(
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

tff(c_24,plain,(
    ~ v2_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    v5_funct_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    k1_relat_1('#skF_5') = k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_67,plain,(
    ! [A_33] :
      ( r2_hidden('#skF_2'(A_33),k1_relat_1(A_33))
      | v2_relat_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_70,plain,
    ( r2_hidden('#skF_2'('#skF_5'),k1_relat_1('#skF_4'))
    | v2_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_67])).

tff(c_72,plain,
    ( r2_hidden('#skF_2'('#skF_5'),k1_relat_1('#skF_4'))
    | v2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_70])).

tff(c_73,plain,(
    r2_hidden('#skF_2'('#skF_5'),k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_72])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50,plain,(
    ! [A_27,B_28,C_29] :
      ( ~ r1_xboole_0(A_27,B_28)
      | ~ r2_hidden(C_29,k3_xboole_0(A_27,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_53,plain,(
    ! [A_7,C_29] :
      ( ~ r1_xboole_0(A_7,k1_xboole_0)
      | ~ r2_hidden(C_29,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_50])).

tff(c_55,plain,(
    ! [C_29] : ~ r2_hidden(C_29,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_53])).

tff(c_74,plain,(
    ! [A_34] :
      ( v1_xboole_0(k1_funct_1(A_34,'#skF_2'(A_34)))
      | v2_relat_1(A_34)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [A_34] :
      ( k1_funct_1(A_34,'#skF_2'(A_34)) = k1_xboole_0
      | v2_relat_1(A_34)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(resolution,[status(thm)],[c_74,c_2])).

tff(c_132,plain,(
    ! [B_43,C_44,A_45] :
      ( r2_hidden(k1_funct_1(B_43,C_44),k1_funct_1(A_45,C_44))
      | ~ r2_hidden(C_44,k1_relat_1(B_43))
      | ~ v5_funct_1(B_43,A_45)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_138,plain,(
    ! [B_43,A_34] :
      ( r2_hidden(k1_funct_1(B_43,'#skF_2'(A_34)),k1_xboole_0)
      | ~ r2_hidden('#skF_2'(A_34),k1_relat_1(B_43))
      | ~ v5_funct_1(B_43,A_34)
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34)
      | v2_relat_1(A_34)
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_132])).

tff(c_146,plain,(
    ! [A_48,B_49] :
      ( ~ r2_hidden('#skF_2'(A_48),k1_relat_1(B_49))
      | ~ v5_funct_1(B_49,A_48)
      | ~ v1_funct_1(B_49)
      | ~ v1_relat_1(B_49)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48)
      | v2_relat_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_138])).

tff(c_149,plain,
    ( ~ v5_funct_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | v2_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_73,c_146])).

tff(c_158,plain,(
    v2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_36,c_34,c_28,c_149])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:28:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.21  
% 2.04/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.21  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1
% 2.04/1.21  
% 2.04/1.21  %Foreground sorts:
% 2.04/1.21  
% 2.04/1.21  
% 2.04/1.21  %Background operators:
% 2.04/1.21  
% 2.04/1.21  
% 2.04/1.21  %Foreground operators:
% 2.04/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.04/1.21  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.04/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.21  tff(v2_relat_1, type, v2_relat_1: $i > $o).
% 2.04/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.04/1.21  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.04/1.21  tff('#skF_5', type, '#skF_5': $i).
% 2.04/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.04/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.04/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.04/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.04/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.04/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.21  
% 2.04/1.22  tff(f_91, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v5_funct_1(A, B) & (k1_relat_1(A) = k1_relat_1(B))) => v2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_funct_1)).
% 2.04/1.22  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_relat_1(A) <=> (![B]: ~(r2_hidden(B, k1_relat_1(A)) & v1_xboole_0(k1_funct_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_funct_1)).
% 2.04/1.22  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.04/1.22  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.04/1.22  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.04/1.22  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.04/1.22  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.04/1.22  tff(c_24, plain, (~v2_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.04/1.22  tff(c_32, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.04/1.22  tff(c_30, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.04/1.22  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.04/1.22  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.04/1.22  tff(c_28, plain, (v5_funct_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.04/1.22  tff(c_26, plain, (k1_relat_1('#skF_5')=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.04/1.22  tff(c_67, plain, (![A_33]: (r2_hidden('#skF_2'(A_33), k1_relat_1(A_33)) | v2_relat_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.04/1.22  tff(c_70, plain, (r2_hidden('#skF_2'('#skF_5'), k1_relat_1('#skF_4')) | v2_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_26, c_67])).
% 2.04/1.22  tff(c_72, plain, (r2_hidden('#skF_2'('#skF_5'), k1_relat_1('#skF_4')) | v2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_70])).
% 2.04/1.22  tff(c_73, plain, (r2_hidden('#skF_2'('#skF_5'), k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_24, c_72])).
% 2.04/1.22  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.04/1.22  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.04/1.22  tff(c_50, plain, (![A_27, B_28, C_29]: (~r1_xboole_0(A_27, B_28) | ~r2_hidden(C_29, k3_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.04/1.22  tff(c_53, plain, (![A_7, C_29]: (~r1_xboole_0(A_7, k1_xboole_0) | ~r2_hidden(C_29, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_50])).
% 2.04/1.22  tff(c_55, plain, (![C_29]: (~r2_hidden(C_29, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_53])).
% 2.04/1.22  tff(c_74, plain, (![A_34]: (v1_xboole_0(k1_funct_1(A_34, '#skF_2'(A_34))) | v2_relat_1(A_34) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.04/1.22  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.22  tff(c_78, plain, (![A_34]: (k1_funct_1(A_34, '#skF_2'(A_34))=k1_xboole_0 | v2_relat_1(A_34) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(resolution, [status(thm)], [c_74, c_2])).
% 2.04/1.22  tff(c_132, plain, (![B_43, C_44, A_45]: (r2_hidden(k1_funct_1(B_43, C_44), k1_funct_1(A_45, C_44)) | ~r2_hidden(C_44, k1_relat_1(B_43)) | ~v5_funct_1(B_43, A_45) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.04/1.22  tff(c_138, plain, (![B_43, A_34]: (r2_hidden(k1_funct_1(B_43, '#skF_2'(A_34)), k1_xboole_0) | ~r2_hidden('#skF_2'(A_34), k1_relat_1(B_43)) | ~v5_funct_1(B_43, A_34) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34) | v2_relat_1(A_34) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_78, c_132])).
% 2.04/1.22  tff(c_146, plain, (![A_48, B_49]: (~r2_hidden('#skF_2'(A_48), k1_relat_1(B_49)) | ~v5_funct_1(B_49, A_48) | ~v1_funct_1(B_49) | ~v1_relat_1(B_49) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48) | v2_relat_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(negUnitSimplification, [status(thm)], [c_55, c_138])).
% 2.04/1.22  tff(c_149, plain, (~v5_funct_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v2_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_73, c_146])).
% 2.04/1.22  tff(c_158, plain, (v2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_36, c_34, c_28, c_149])).
% 2.04/1.22  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_158])).
% 2.04/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.22  
% 2.04/1.22  Inference rules
% 2.04/1.22  ----------------------
% 2.04/1.22  #Ref     : 0
% 2.04/1.22  #Sup     : 25
% 2.04/1.22  #Fact    : 0
% 2.04/1.22  #Define  : 0
% 2.04/1.22  #Split   : 2
% 2.04/1.22  #Chain   : 0
% 2.04/1.22  #Close   : 0
% 2.04/1.22  
% 2.04/1.22  Ordering : KBO
% 2.04/1.22  
% 2.04/1.22  Simplification rules
% 2.04/1.22  ----------------------
% 2.04/1.22  #Subsume      : 2
% 2.04/1.22  #Demod        : 17
% 2.04/1.22  #Tautology    : 11
% 2.04/1.22  #SimpNegUnit  : 4
% 2.04/1.22  #BackRed      : 0
% 2.04/1.22  
% 2.04/1.22  #Partial instantiations: 0
% 2.04/1.22  #Strategies tried      : 1
% 2.04/1.22  
% 2.04/1.22  Timing (in seconds)
% 2.04/1.22  ----------------------
% 2.04/1.23  Preprocessing        : 0.30
% 2.04/1.23  Parsing              : 0.16
% 2.04/1.23  CNF conversion       : 0.02
% 2.04/1.23  Main loop            : 0.17
% 2.04/1.23  Inferencing          : 0.07
% 2.04/1.23  Reduction            : 0.05
% 2.04/1.23  Demodulation         : 0.04
% 2.04/1.23  BG Simplification    : 0.01
% 2.04/1.23  Subsumption          : 0.03
% 2.04/1.23  Abstraction          : 0.01
% 2.04/1.23  MUC search           : 0.00
% 2.04/1.23  Cooper               : 0.00
% 2.04/1.23  Total                : 0.51
% 2.04/1.23  Index Insertion      : 0.00
% 2.04/1.23  Index Deletion       : 0.00
% 2.04/1.23  Index Matching       : 0.00
% 2.04/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
