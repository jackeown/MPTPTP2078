%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:51 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   54 (  94 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 191 expanded)
%              Number of equality atoms :   21 (  79 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_82,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_46,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_70,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_102,plain,(
    ! [A_33,B_34,C_35] :
      ( ~ r1_xboole_0(A_33,B_34)
      | ~ r2_hidden(C_35,k3_xboole_0(A_33,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_105,plain,(
    ! [A_6,C_35] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_35,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_102])).

tff(c_107,plain,(
    ! [C_35] : ~ r2_hidden(C_35,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_105])).

tff(c_26,plain,(
    ! [A_19] : k1_relat_1('#skF_3'(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    ! [A_19] : v1_relat_1('#skF_3'(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_74,plain,(
    ! [A_31] :
      ( k1_relat_1(A_31) != k1_xboole_0
      | k1_xboole_0 = A_31
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_77,plain,(
    ! [A_19] :
      ( k1_relat_1('#skF_3'(A_19)) != k1_xboole_0
      | '#skF_3'(A_19) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_74])).

tff(c_85,plain,(
    ! [A_32] :
      ( k1_xboole_0 != A_32
      | '#skF_3'(A_32) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_77])).

tff(c_95,plain,(
    ! [A_32] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_32 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_30])).

tff(c_119,plain,(
    ! [A_32] : k1_xboole_0 != A_32 ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_6])).

tff(c_127,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_28,plain,(
    ! [A_19] : v1_funct_1('#skF_3'(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_93,plain,(
    ! [A_32] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_32 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_28])).

tff(c_109,plain,(
    ! [A_32] : k1_xboole_0 != A_32 ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_6])).

tff(c_117,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_176,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_2'(A_44,B_45),k1_relat_1(B_45))
      | v5_funct_1(B_45,A_44)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_185,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_2'(A_44,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_44)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_176])).

tff(c_190,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_2'(A_44,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_117,c_185])).

tff(c_192,plain,(
    ! [A_46] :
      ( v5_funct_1(k1_xboole_0,A_46)
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_190])).

tff(c_32,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_195,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_192,c_32])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.22  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 1.98/1.22  
% 1.98/1.22  %Foreground sorts:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Background operators:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Foreground operators:
% 1.98/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.22  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.98/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.22  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.98/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.22  
% 2.10/1.23  tff(f_89, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 2.10/1.23  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.10/1.23  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.10/1.23  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.10/1.23  tff(f_82, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.10/1.23  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.10/1.23  tff(f_46, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.10/1.23  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.10/1.23  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.10/1.23  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.10/1.23  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.23  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.23  tff(c_102, plain, (![A_33, B_34, C_35]: (~r1_xboole_0(A_33, B_34) | ~r2_hidden(C_35, k3_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.23  tff(c_105, plain, (![A_6, C_35]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_35, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_102])).
% 2.10/1.23  tff(c_107, plain, (![C_35]: (~r2_hidden(C_35, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_105])).
% 2.10/1.23  tff(c_26, plain, (![A_19]: (k1_relat_1('#skF_3'(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.10/1.23  tff(c_30, plain, (![A_19]: (v1_relat_1('#skF_3'(A_19)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.10/1.23  tff(c_74, plain, (![A_31]: (k1_relat_1(A_31)!=k1_xboole_0 | k1_xboole_0=A_31 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.10/1.23  tff(c_77, plain, (![A_19]: (k1_relat_1('#skF_3'(A_19))!=k1_xboole_0 | '#skF_3'(A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_74])).
% 2.10/1.23  tff(c_85, plain, (![A_32]: (k1_xboole_0!=A_32 | '#skF_3'(A_32)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_77])).
% 2.10/1.23  tff(c_95, plain, (![A_32]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_32)), inference(superposition, [status(thm), theory('equality')], [c_85, c_30])).
% 2.10/1.23  tff(c_119, plain, (![A_32]: (k1_xboole_0!=A_32)), inference(splitLeft, [status(thm)], [c_95])).
% 2.10/1.23  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_6])).
% 2.10/1.23  tff(c_127, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_95])).
% 2.10/1.23  tff(c_28, plain, (![A_19]: (v1_funct_1('#skF_3'(A_19)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.10/1.23  tff(c_93, plain, (![A_32]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_32)), inference(superposition, [status(thm), theory('equality')], [c_85, c_28])).
% 2.10/1.23  tff(c_109, plain, (![A_32]: (k1_xboole_0!=A_32)), inference(splitLeft, [status(thm)], [c_93])).
% 2.10/1.23  tff(c_116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_6])).
% 2.10/1.23  tff(c_117, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_93])).
% 2.10/1.23  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.10/1.23  tff(c_176, plain, (![A_44, B_45]: (r2_hidden('#skF_2'(A_44, B_45), k1_relat_1(B_45)) | v5_funct_1(B_45, A_44) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.10/1.23  tff(c_185, plain, (![A_44]: (r2_hidden('#skF_2'(A_44, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_44) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_12, c_176])).
% 2.10/1.23  tff(c_190, plain, (![A_44]: (r2_hidden('#skF_2'(A_44, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_117, c_185])).
% 2.10/1.23  tff(c_192, plain, (![A_46]: (v5_funct_1(k1_xboole_0, A_46) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(negUnitSimplification, [status(thm)], [c_107, c_190])).
% 2.10/1.23  tff(c_32, plain, (~v5_funct_1(k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.10/1.23  tff(c_195, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_192, c_32])).
% 2.10/1.23  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_195])).
% 2.10/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.23  
% 2.10/1.23  Inference rules
% 2.10/1.23  ----------------------
% 2.10/1.23  #Ref     : 0
% 2.10/1.23  #Sup     : 31
% 2.10/1.23  #Fact    : 0
% 2.10/1.23  #Define  : 0
% 2.10/1.23  #Split   : 4
% 2.10/1.23  #Chain   : 0
% 2.10/1.23  #Close   : 0
% 2.10/1.23  
% 2.10/1.23  Ordering : KBO
% 2.10/1.23  
% 2.10/1.23  Simplification rules
% 2.10/1.23  ----------------------
% 2.10/1.23  #Subsume      : 10
% 2.10/1.23  #Demod        : 13
% 2.10/1.23  #Tautology    : 17
% 2.10/1.23  #SimpNegUnit  : 14
% 2.10/1.23  #BackRed      : 6
% 2.10/1.23  
% 2.10/1.23  #Partial instantiations: 0
% 2.10/1.23  #Strategies tried      : 1
% 2.10/1.23  
% 2.10/1.23  Timing (in seconds)
% 2.10/1.23  ----------------------
% 2.10/1.23  Preprocessing        : 0.29
% 2.10/1.23  Parsing              : 0.17
% 2.10/1.23  CNF conversion       : 0.02
% 2.10/1.23  Main loop            : 0.17
% 2.10/1.23  Inferencing          : 0.07
% 2.10/1.23  Reduction            : 0.05
% 2.10/1.23  Demodulation         : 0.04
% 2.10/1.23  BG Simplification    : 0.01
% 2.10/1.23  Subsumption          : 0.03
% 2.10/1.23  Abstraction          : 0.01
% 2.10/1.23  MUC search           : 0.00
% 2.10/1.23  Cooper               : 0.00
% 2.10/1.23  Total                : 0.50
% 2.10/1.23  Index Insertion      : 0.00
% 2.10/1.23  Index Deletion       : 0.00
% 2.13/1.23  Index Matching       : 0.00
% 2.13/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
