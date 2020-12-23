%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:50 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   55 (  95 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 191 expanded)
%              Number of equality atoms :   21 (  79 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > o_1_0_funct_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_1_0_funct_1,type,(
    o_1_0_funct_1: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = B
      & ! [D] :
          ( r2_hidden(D,B)
         => k1_funct_1(C,D) = o_1_0_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e1_27_1__funct_1)).

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

tff(c_85,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,k3_xboole_0(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_88,plain,(
    ! [A_6,C_38] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_38,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_85])).

tff(c_90,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_88])).

tff(c_26,plain,(
    ! [A_19,B_20] : k1_relat_1('#skF_3'(A_19,B_20)) = B_20 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    ! [A_19,B_20] : v1_relat_1('#skF_3'(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_74,plain,(
    ! [A_35] :
      ( k1_relat_1(A_35) != k1_xboole_0
      | k1_xboole_0 = A_35
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_77,plain,(
    ! [A_19,B_20] :
      ( k1_relat_1('#skF_3'(A_19,B_20)) != k1_xboole_0
      | '#skF_3'(A_19,B_20) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_74])).

tff(c_93,plain,(
    ! [B_40,A_41] :
      ( k1_xboole_0 != B_40
      | '#skF_3'(A_41,B_40) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_77])).

tff(c_101,plain,(
    ! [B_40] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != B_40 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_30])).

tff(c_120,plain,(
    ! [B_40] : k1_xboole_0 != B_40 ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_6])).

tff(c_128,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_28,plain,(
    ! [A_19,B_20] : v1_funct_1('#skF_3'(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_103,plain,(
    ! [B_40] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != B_40 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_28])).

tff(c_143,plain,(
    ! [B_40] : k1_xboole_0 != B_40 ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_6])).

tff(c_151,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_175,plain,(
    ! [A_52,B_53] :
      ( r2_hidden('#skF_2'(A_52,B_53),k1_relat_1(B_53))
      | v5_funct_1(B_53,A_52)
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_183,plain,(
    ! [A_52] :
      ( r2_hidden('#skF_2'(A_52,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_52)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_175])).

tff(c_188,plain,(
    ! [A_52] :
      ( r2_hidden('#skF_2'(A_52,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_52)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_151,c_183])).

tff(c_190,plain,(
    ! [A_54] :
      ( v5_funct_1(k1_xboole_0,A_54)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_188])).

tff(c_32,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_193,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_190,c_32])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:01:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.29  
% 2.04/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.29  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_xboole_0 > k1_funct_1 > #nlpp > o_1_0_funct_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.04/1.29  
% 2.04/1.29  %Foreground sorts:
% 2.04/1.29  
% 2.04/1.29  
% 2.04/1.29  %Background operators:
% 2.04/1.29  
% 2.04/1.29  
% 2.04/1.29  %Foreground operators:
% 2.04/1.29  tff(o_1_0_funct_1, type, o_1_0_funct_1: $i > $i).
% 2.04/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.04/1.29  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.04/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.04/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.04/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.04/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.04/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.04/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.29  
% 2.04/1.30  tff(f_89, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 2.04/1.30  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.04/1.30  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.04/1.30  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.04/1.30  tff(f_82, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = B)) & (![D]: (r2_hidden(D, B) => (k1_funct_1(C, D) = o_1_0_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e1_27_1__funct_1)).
% 2.04/1.30  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.04/1.30  tff(f_46, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.04/1.30  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.04/1.30  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.04/1.30  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.04/1.30  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.04/1.30  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.30  tff(c_85, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, k3_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.04/1.30  tff(c_88, plain, (![A_6, C_38]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_85])).
% 2.04/1.30  tff(c_90, plain, (![C_38]: (~r2_hidden(C_38, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_88])).
% 2.04/1.30  tff(c_26, plain, (![A_19, B_20]: (k1_relat_1('#skF_3'(A_19, B_20))=B_20)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.04/1.30  tff(c_30, plain, (![A_19, B_20]: (v1_relat_1('#skF_3'(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.04/1.30  tff(c_74, plain, (![A_35]: (k1_relat_1(A_35)!=k1_xboole_0 | k1_xboole_0=A_35 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.04/1.30  tff(c_77, plain, (![A_19, B_20]: (k1_relat_1('#skF_3'(A_19, B_20))!=k1_xboole_0 | '#skF_3'(A_19, B_20)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_74])).
% 2.04/1.30  tff(c_93, plain, (![B_40, A_41]: (k1_xboole_0!=B_40 | '#skF_3'(A_41, B_40)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_77])).
% 2.04/1.30  tff(c_101, plain, (![B_40]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=B_40)), inference(superposition, [status(thm), theory('equality')], [c_93, c_30])).
% 2.04/1.30  tff(c_120, plain, (![B_40]: (k1_xboole_0!=B_40)), inference(splitLeft, [status(thm)], [c_101])).
% 2.04/1.30  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_6])).
% 2.04/1.30  tff(c_128, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_101])).
% 2.04/1.30  tff(c_28, plain, (![A_19, B_20]: (v1_funct_1('#skF_3'(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.04/1.30  tff(c_103, plain, (![B_40]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=B_40)), inference(superposition, [status(thm), theory('equality')], [c_93, c_28])).
% 2.04/1.30  tff(c_143, plain, (![B_40]: (k1_xboole_0!=B_40)), inference(splitLeft, [status(thm)], [c_103])).
% 2.04/1.30  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_6])).
% 2.04/1.30  tff(c_151, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_103])).
% 2.04/1.30  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.04/1.30  tff(c_175, plain, (![A_52, B_53]: (r2_hidden('#skF_2'(A_52, B_53), k1_relat_1(B_53)) | v5_funct_1(B_53, A_52) | ~v1_funct_1(B_53) | ~v1_relat_1(B_53) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.04/1.30  tff(c_183, plain, (![A_52]: (r2_hidden('#skF_2'(A_52, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_52) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(superposition, [status(thm), theory('equality')], [c_12, c_175])).
% 2.04/1.30  tff(c_188, plain, (![A_52]: (r2_hidden('#skF_2'(A_52, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_52) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_151, c_183])).
% 2.04/1.30  tff(c_190, plain, (![A_54]: (v5_funct_1(k1_xboole_0, A_54) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(negUnitSimplification, [status(thm)], [c_90, c_188])).
% 2.04/1.30  tff(c_32, plain, (~v5_funct_1(k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.04/1.30  tff(c_193, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_190, c_32])).
% 2.04/1.30  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_193])).
% 2.04/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.30  
% 2.04/1.30  Inference rules
% 2.04/1.30  ----------------------
% 2.04/1.30  #Ref     : 0
% 2.04/1.30  #Sup     : 31
% 2.04/1.30  #Fact    : 0
% 2.04/1.30  #Define  : 0
% 2.04/1.30  #Split   : 4
% 2.04/1.30  #Chain   : 0
% 2.04/1.30  #Close   : 0
% 2.04/1.30  
% 2.04/1.30  Ordering : KBO
% 2.04/1.30  
% 2.04/1.30  Simplification rules
% 2.04/1.30  ----------------------
% 2.04/1.30  #Subsume      : 11
% 2.04/1.30  #Demod        : 13
% 2.04/1.30  #Tautology    : 17
% 2.04/1.30  #SimpNegUnit  : 14
% 2.04/1.30  #BackRed      : 6
% 2.04/1.30  
% 2.04/1.30  #Partial instantiations: 0
% 2.04/1.31  #Strategies tried      : 1
% 2.04/1.31  
% 2.04/1.31  Timing (in seconds)
% 2.04/1.31  ----------------------
% 2.04/1.31  Preprocessing        : 0.30
% 2.04/1.31  Parsing              : 0.17
% 2.04/1.31  CNF conversion       : 0.02
% 2.04/1.31  Main loop            : 0.17
% 2.04/1.31  Inferencing          : 0.07
% 2.04/1.31  Reduction            : 0.05
% 2.04/1.31  Demodulation         : 0.04
% 2.04/1.31  BG Simplification    : 0.01
% 2.04/1.31  Subsumption          : 0.03
% 2.04/1.31  Abstraction          : 0.01
% 2.04/1.31  MUC search           : 0.00
% 2.04/1.31  Cooper               : 0.00
% 2.04/1.31  Total                : 0.50
% 2.04/1.31  Index Insertion      : 0.00
% 2.04/1.31  Index Deletion       : 0.00
% 2.04/1.31  Index Matching       : 0.00
% 2.04/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
