%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:16 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 164 expanded)
%              Number of leaves         :   19 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :   80 ( 450 expanded)
%              Number of equality atoms :   11 (  51 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_28,plain,(
    k10_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [A_7,B_30,C_31] :
      ( r2_hidden('#skF_3'(A_7,B_30,C_31),B_30)
      | r2_hidden('#skF_4'(A_7,B_30,C_31),C_31)
      | k10_relat_1(A_7,B_30) = C_31
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_106,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden('#skF_3'(A_76,B_77,C_78),B_77)
      | r2_hidden('#skF_4'(A_76,B_77,C_78),C_78)
      | k10_relat_1(A_76,B_77) = C_78
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,B_55)
      | ~ r2_hidden(C_56,A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_37,plain,(
    ! [C_56,A_6] :
      ( ~ r2_hidden(C_56,k1_xboole_0)
      | ~ r2_hidden(C_56,A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_34])).

tff(c_341,plain,(
    ! [A_141,B_142,A_143] :
      ( ~ r2_hidden('#skF_4'(A_141,B_142,k1_xboole_0),A_143)
      | r2_hidden('#skF_3'(A_141,B_142,k1_xboole_0),B_142)
      | k10_relat_1(A_141,B_142) = k1_xboole_0
      | ~ v1_relat_1(A_141) ) ),
    inference(resolution,[status(thm)],[c_106,c_37])).

tff(c_349,plain,(
    ! [A_7,B_30] :
      ( r2_hidden('#skF_3'(A_7,B_30,k1_xboole_0),B_30)
      | k10_relat_1(A_7,B_30) = k1_xboole_0
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_24,c_341])).

tff(c_351,plain,(
    ! [A_148,B_149] :
      ( r2_hidden('#skF_3'(A_148,B_149,k1_xboole_0),B_149)
      | k10_relat_1(A_148,B_149) = k1_xboole_0
      | ~ v1_relat_1(A_148) ) ),
    inference(resolution,[status(thm)],[c_24,c_341])).

tff(c_12,plain,(
    ! [A_7,B_30,D_45] :
      ( r2_hidden('#skF_5'(A_7,B_30,k10_relat_1(A_7,B_30),D_45),B_30)
      | ~ r2_hidden(D_45,k10_relat_1(A_7,B_30))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_72,plain,(
    ! [A_66,B_67,D_68] :
      ( r2_hidden('#skF_5'(A_66,B_67,k10_relat_1(A_66,B_67),D_68),B_67)
      | ~ r2_hidden(D_68,k10_relat_1(A_66,B_67))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_80,plain,(
    ! [A_69,D_70,A_71] :
      ( ~ r2_hidden('#skF_5'(A_69,k1_xboole_0,k10_relat_1(A_69,k1_xboole_0),D_70),A_71)
      | ~ r2_hidden(D_70,k10_relat_1(A_69,k1_xboole_0))
      | ~ v1_relat_1(A_69) ) ),
    inference(resolution,[status(thm)],[c_72,c_37])).

tff(c_85,plain,(
    ! [D_45,A_7] :
      ( ~ r2_hidden(D_45,k10_relat_1(A_7,k1_xboole_0))
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_80])).

tff(c_384,plain,(
    ! [A_150,A_151] :
      ( ~ v1_relat_1(A_150)
      | k10_relat_1(A_151,k10_relat_1(A_150,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_151) ) ),
    inference(resolution,[status(thm)],[c_351,c_85])).

tff(c_86,plain,(
    ! [D_72,A_73] :
      ( ~ r2_hidden(D_72,k10_relat_1(A_73,k1_xboole_0))
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_12,c_80])).

tff(c_99,plain,(
    ! [A_73,D_45,A_7] :
      ( ~ v1_relat_1(A_73)
      | ~ r2_hidden(D_45,k10_relat_1(A_7,k10_relat_1(A_73,k1_xboole_0)))
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_86])).

tff(c_444,plain,(
    ! [A_150,D_45,A_151] :
      ( ~ v1_relat_1(A_150)
      | ~ r2_hidden(D_45,k1_xboole_0)
      | ~ v1_relat_1(A_151)
      | ~ v1_relat_1(A_150)
      | ~ v1_relat_1(A_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_99])).

tff(c_493,plain,(
    ! [A_155] :
      ( ~ v1_relat_1(A_155)
      | ~ v1_relat_1(A_155) ) ),
    inference(splitLeft,[status(thm)],[c_444])).

tff(c_495,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_493])).

tff(c_499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_495])).

tff(c_500,plain,(
    ! [D_45,A_150] :
      ( ~ r2_hidden(D_45,k1_xboole_0)
      | ~ v1_relat_1(A_150)
      | ~ v1_relat_1(A_150) ) ),
    inference(splitRight,[status(thm)],[c_444])).

tff(c_502,plain,(
    ! [A_156] :
      ( ~ v1_relat_1(A_156)
      | ~ v1_relat_1(A_156) ) ),
    inference(splitLeft,[status(thm)],[c_500])).

tff(c_504,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_30,c_502])).

tff(c_508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_504])).

tff(c_510,plain,(
    ! [D_157] : ~ r2_hidden(D_157,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_550,plain,(
    ! [A_158] :
      ( k10_relat_1(A_158,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_158) ) ),
    inference(resolution,[status(thm)],[c_349,c_510])).

tff(c_553,plain,(
    k10_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_550])).

tff(c_557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_553])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:46:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.33  
% 2.55/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.33  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1
% 2.55/1.33  
% 2.55/1.33  %Foreground sorts:
% 2.55/1.33  
% 2.55/1.33  
% 2.55/1.33  %Background operators:
% 2.55/1.33  
% 2.55/1.33  
% 2.55/1.33  %Foreground operators:
% 2.55/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.55/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.55/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.55/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.55/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.55/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.55/1.33  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.55/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.55/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.55/1.33  
% 2.55/1.34  tff(f_63, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 2.55/1.34  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 2.55/1.34  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.55/1.34  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.55/1.34  tff(c_28, plain, (k10_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.55/1.34  tff(c_30, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.55/1.34  tff(c_24, plain, (![A_7, B_30, C_31]: (r2_hidden('#skF_3'(A_7, B_30, C_31), B_30) | r2_hidden('#skF_4'(A_7, B_30, C_31), C_31) | k10_relat_1(A_7, B_30)=C_31 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.55/1.34  tff(c_106, plain, (![A_76, B_77, C_78]: (r2_hidden('#skF_3'(A_76, B_77, C_78), B_77) | r2_hidden('#skF_4'(A_76, B_77, C_78), C_78) | k10_relat_1(A_76, B_77)=C_78 | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.55/1.34  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.55/1.34  tff(c_34, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, B_55) | ~r2_hidden(C_56, A_54))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.55/1.34  tff(c_37, plain, (![C_56, A_6]: (~r2_hidden(C_56, k1_xboole_0) | ~r2_hidden(C_56, A_6))), inference(resolution, [status(thm)], [c_8, c_34])).
% 2.55/1.34  tff(c_341, plain, (![A_141, B_142, A_143]: (~r2_hidden('#skF_4'(A_141, B_142, k1_xboole_0), A_143) | r2_hidden('#skF_3'(A_141, B_142, k1_xboole_0), B_142) | k10_relat_1(A_141, B_142)=k1_xboole_0 | ~v1_relat_1(A_141))), inference(resolution, [status(thm)], [c_106, c_37])).
% 2.55/1.34  tff(c_349, plain, (![A_7, B_30]: (r2_hidden('#skF_3'(A_7, B_30, k1_xboole_0), B_30) | k10_relat_1(A_7, B_30)=k1_xboole_0 | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_24, c_341])).
% 2.55/1.34  tff(c_351, plain, (![A_148, B_149]: (r2_hidden('#skF_3'(A_148, B_149, k1_xboole_0), B_149) | k10_relat_1(A_148, B_149)=k1_xboole_0 | ~v1_relat_1(A_148))), inference(resolution, [status(thm)], [c_24, c_341])).
% 2.55/1.34  tff(c_12, plain, (![A_7, B_30, D_45]: (r2_hidden('#skF_5'(A_7, B_30, k10_relat_1(A_7, B_30), D_45), B_30) | ~r2_hidden(D_45, k10_relat_1(A_7, B_30)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.55/1.34  tff(c_72, plain, (![A_66, B_67, D_68]: (r2_hidden('#skF_5'(A_66, B_67, k10_relat_1(A_66, B_67), D_68), B_67) | ~r2_hidden(D_68, k10_relat_1(A_66, B_67)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.55/1.34  tff(c_80, plain, (![A_69, D_70, A_71]: (~r2_hidden('#skF_5'(A_69, k1_xboole_0, k10_relat_1(A_69, k1_xboole_0), D_70), A_71) | ~r2_hidden(D_70, k10_relat_1(A_69, k1_xboole_0)) | ~v1_relat_1(A_69))), inference(resolution, [status(thm)], [c_72, c_37])).
% 2.55/1.34  tff(c_85, plain, (![D_45, A_7]: (~r2_hidden(D_45, k10_relat_1(A_7, k1_xboole_0)) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_12, c_80])).
% 2.55/1.34  tff(c_384, plain, (![A_150, A_151]: (~v1_relat_1(A_150) | k10_relat_1(A_151, k10_relat_1(A_150, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_151))), inference(resolution, [status(thm)], [c_351, c_85])).
% 2.55/1.34  tff(c_86, plain, (![D_72, A_73]: (~r2_hidden(D_72, k10_relat_1(A_73, k1_xboole_0)) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_12, c_80])).
% 2.55/1.34  tff(c_99, plain, (![A_73, D_45, A_7]: (~v1_relat_1(A_73) | ~r2_hidden(D_45, k10_relat_1(A_7, k10_relat_1(A_73, k1_xboole_0))) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_12, c_86])).
% 2.55/1.34  tff(c_444, plain, (![A_150, D_45, A_151]: (~v1_relat_1(A_150) | ~r2_hidden(D_45, k1_xboole_0) | ~v1_relat_1(A_151) | ~v1_relat_1(A_150) | ~v1_relat_1(A_151))), inference(superposition, [status(thm), theory('equality')], [c_384, c_99])).
% 2.55/1.34  tff(c_493, plain, (![A_155]: (~v1_relat_1(A_155) | ~v1_relat_1(A_155))), inference(splitLeft, [status(thm)], [c_444])).
% 2.55/1.34  tff(c_495, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_493])).
% 2.55/1.34  tff(c_499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_495])).
% 2.55/1.34  tff(c_500, plain, (![D_45, A_150]: (~r2_hidden(D_45, k1_xboole_0) | ~v1_relat_1(A_150) | ~v1_relat_1(A_150))), inference(splitRight, [status(thm)], [c_444])).
% 2.55/1.34  tff(c_502, plain, (![A_156]: (~v1_relat_1(A_156) | ~v1_relat_1(A_156))), inference(splitLeft, [status(thm)], [c_500])).
% 2.55/1.34  tff(c_504, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_30, c_502])).
% 2.55/1.34  tff(c_508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_504])).
% 2.55/1.34  tff(c_510, plain, (![D_157]: (~r2_hidden(D_157, k1_xboole_0))), inference(splitRight, [status(thm)], [c_500])).
% 2.55/1.34  tff(c_550, plain, (![A_158]: (k10_relat_1(A_158, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_158))), inference(resolution, [status(thm)], [c_349, c_510])).
% 2.55/1.34  tff(c_553, plain, (k10_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_550])).
% 2.55/1.34  tff(c_557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_553])).
% 2.55/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.34  
% 2.55/1.34  Inference rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Ref     : 0
% 2.55/1.34  #Sup     : 109
% 2.55/1.34  #Fact    : 0
% 2.55/1.34  #Define  : 0
% 2.55/1.34  #Split   : 2
% 2.55/1.34  #Chain   : 0
% 2.55/1.34  #Close   : 0
% 2.55/1.34  
% 2.55/1.34  Ordering : KBO
% 2.55/1.34  
% 2.55/1.34  Simplification rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Subsume      : 30
% 2.55/1.34  #Demod        : 13
% 2.55/1.34  #Tautology    : 13
% 2.55/1.34  #SimpNegUnit  : 1
% 2.55/1.34  #BackRed      : 0
% 2.55/1.34  
% 2.55/1.34  #Partial instantiations: 0
% 2.55/1.34  #Strategies tried      : 1
% 2.55/1.34  
% 2.55/1.34  Timing (in seconds)
% 2.55/1.34  ----------------------
% 2.55/1.35  Preprocessing        : 0.28
% 2.55/1.35  Parsing              : 0.15
% 2.55/1.35  CNF conversion       : 0.03
% 2.55/1.35  Main loop            : 0.32
% 2.55/1.35  Inferencing          : 0.13
% 2.55/1.35  Reduction            : 0.07
% 2.55/1.35  Demodulation         : 0.05
% 2.55/1.35  BG Simplification    : 0.02
% 2.55/1.35  Subsumption          : 0.08
% 2.55/1.35  Abstraction          : 0.01
% 2.55/1.35  MUC search           : 0.00
% 2.55/1.35  Cooper               : 0.00
% 2.55/1.35  Total                : 0.62
% 2.55/1.35  Index Insertion      : 0.00
% 2.55/1.35  Index Deletion       : 0.00
% 2.55/1.35  Index Matching       : 0.00
% 2.55/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
