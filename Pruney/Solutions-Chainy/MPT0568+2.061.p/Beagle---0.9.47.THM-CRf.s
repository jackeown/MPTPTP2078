%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:28 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   50 (  97 expanded)
%              Number of leaves         :   24 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :   68 ( 161 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_1 > #skF_3 > #skF_7 > #skF_8 > #skF_2 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_63,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_4'(A_34),A_34)
      | v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(A_35)
      | v1_relat_1(A_35) ) ),
    inference(resolution,[status(thm)],[c_32,c_2])).

tff(c_41,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_37])).

tff(c_321,plain,(
    ! [A_77,B_78,C_79] :
      ( r2_hidden(k4_tarski(A_77,'#skF_7'(A_77,B_78,C_79)),C_79)
      | ~ r2_hidden(A_77,k10_relat_1(C_79,B_78))
      | ~ v1_relat_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_106,plain,(
    ! [A_55,B_56,C_57] :
      ( r2_hidden('#skF_7'(A_55,B_56,C_57),B_56)
      | ~ r2_hidden(A_55,k10_relat_1(C_57,B_56))
      | ~ v1_relat_1(C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_111,plain,(
    ! [B_58,A_59,C_60] :
      ( ~ v1_xboole_0(B_58)
      | ~ r2_hidden(A_59,k10_relat_1(C_60,B_58))
      | ~ v1_relat_1(C_60) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_152,plain,(
    ! [B_61,C_62] :
      ( ~ v1_xboole_0(B_61)
      | ~ v1_relat_1(C_62)
      | v1_xboole_0(k10_relat_1(C_62,B_61)) ) ),
    inference(resolution,[status(thm)],[c_4,c_111])).

tff(c_53,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_2'(A_42,B_43),B_43)
      | r2_hidden('#skF_3'(A_42,B_43),A_42)
      | B_43 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    ! [B_44,A_45] :
      ( ~ v1_xboole_0(B_44)
      | r2_hidden('#skF_3'(A_45,B_44),A_45)
      | B_44 = A_45 ) ),
    inference(resolution,[status(thm)],[c_53,c_2])).

tff(c_67,plain,(
    ! [A_46,B_47] :
      ( ~ v1_xboole_0(A_46)
      | ~ v1_xboole_0(B_47)
      | B_47 = A_46 ) ),
    inference(resolution,[status(thm)],[c_62,c_2])).

tff(c_70,plain,(
    ! [B_47] :
      ( ~ v1_xboole_0(B_47)
      | k1_xboole_0 = B_47 ) ),
    inference(resolution,[status(thm)],[c_6,c_67])).

tff(c_175,plain,(
    ! [C_67,B_68] :
      ( k10_relat_1(C_67,B_68) = k1_xboole_0
      | ~ v1_xboole_0(B_68)
      | ~ v1_relat_1(C_67) ) ),
    inference(resolution,[status(thm)],[c_152,c_70])).

tff(c_182,plain,(
    ! [C_69] :
      ( k10_relat_1(C_69,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_69) ) ),
    inference(resolution,[status(thm)],[c_6,c_175])).

tff(c_190,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_41,c_182])).

tff(c_110,plain,(
    ! [B_56,A_55,C_57] :
      ( ~ v1_xboole_0(B_56)
      | ~ r2_hidden(A_55,k10_relat_1(C_57,B_56))
      | ~ v1_relat_1(C_57) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_200,plain,(
    ! [A_55] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_55,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_110])).

tff(c_208,plain,(
    ! [A_55] : ~ r2_hidden(A_55,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_6,c_200])).

tff(c_329,plain,(
    ! [A_77,B_78] :
      ( ~ r2_hidden(A_77,k10_relat_1(k1_xboole_0,B_78))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_321,c_208])).

tff(c_343,plain,(
    ! [A_80,B_81] : ~ r2_hidden(A_80,k10_relat_1(k1_xboole_0,B_81)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_329])).

tff(c_391,plain,(
    ! [B_82] : v1_xboole_0(k10_relat_1(k1_xboole_0,B_82)) ),
    inference(resolution,[status(thm)],[c_4,c_343])).

tff(c_405,plain,(
    ! [B_82] : k10_relat_1(k1_xboole_0,B_82) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_391,c_70])).

tff(c_30,plain,(
    k10_relat_1(k1_xboole_0,'#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:02:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.30  
% 1.99/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.30  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_1 > #skF_3 > #skF_7 > #skF_8 > #skF_2 > #skF_5
% 1.99/1.30  
% 1.99/1.30  %Foreground sorts:
% 1.99/1.30  
% 1.99/1.30  
% 1.99/1.30  %Background operators:
% 1.99/1.30  
% 1.99/1.30  
% 1.99/1.30  %Foreground operators:
% 1.99/1.30  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.99/1.30  tff('#skF_4', type, '#skF_4': $i > $i).
% 1.99/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.99/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.99/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.99/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.30  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 1.99/1.30  tff('#skF_8', type, '#skF_8': $i).
% 1.99/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.99/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.99/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.99/1.30  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.99/1.30  
% 2.23/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.23/1.31  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.23/1.31  tff(f_49, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.23/1.31  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 2.23/1.31  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 2.23/1.31  tff(f_63, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.23/1.31  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.31  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.31  tff(c_32, plain, (![A_34]: (r2_hidden('#skF_4'(A_34), A_34) | v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.31  tff(c_37, plain, (![A_35]: (~v1_xboole_0(A_35) | v1_relat_1(A_35))), inference(resolution, [status(thm)], [c_32, c_2])).
% 2.23/1.31  tff(c_41, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_37])).
% 2.23/1.31  tff(c_321, plain, (![A_77, B_78, C_79]: (r2_hidden(k4_tarski(A_77, '#skF_7'(A_77, B_78, C_79)), C_79) | ~r2_hidden(A_77, k10_relat_1(C_79, B_78)) | ~v1_relat_1(C_79))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.31  tff(c_106, plain, (![A_55, B_56, C_57]: (r2_hidden('#skF_7'(A_55, B_56, C_57), B_56) | ~r2_hidden(A_55, k10_relat_1(C_57, B_56)) | ~v1_relat_1(C_57))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.31  tff(c_111, plain, (![B_58, A_59, C_60]: (~v1_xboole_0(B_58) | ~r2_hidden(A_59, k10_relat_1(C_60, B_58)) | ~v1_relat_1(C_60))), inference(resolution, [status(thm)], [c_106, c_2])).
% 2.23/1.31  tff(c_152, plain, (![B_61, C_62]: (~v1_xboole_0(B_61) | ~v1_relat_1(C_62) | v1_xboole_0(k10_relat_1(C_62, B_61)))), inference(resolution, [status(thm)], [c_4, c_111])).
% 2.23/1.31  tff(c_53, plain, (![A_42, B_43]: (r2_hidden('#skF_2'(A_42, B_43), B_43) | r2_hidden('#skF_3'(A_42, B_43), A_42) | B_43=A_42)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.23/1.31  tff(c_62, plain, (![B_44, A_45]: (~v1_xboole_0(B_44) | r2_hidden('#skF_3'(A_45, B_44), A_45) | B_44=A_45)), inference(resolution, [status(thm)], [c_53, c_2])).
% 2.23/1.31  tff(c_67, plain, (![A_46, B_47]: (~v1_xboole_0(A_46) | ~v1_xboole_0(B_47) | B_47=A_46)), inference(resolution, [status(thm)], [c_62, c_2])).
% 2.23/1.31  tff(c_70, plain, (![B_47]: (~v1_xboole_0(B_47) | k1_xboole_0=B_47)), inference(resolution, [status(thm)], [c_6, c_67])).
% 2.23/1.31  tff(c_175, plain, (![C_67, B_68]: (k10_relat_1(C_67, B_68)=k1_xboole_0 | ~v1_xboole_0(B_68) | ~v1_relat_1(C_67))), inference(resolution, [status(thm)], [c_152, c_70])).
% 2.23/1.31  tff(c_182, plain, (![C_69]: (k10_relat_1(C_69, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_69))), inference(resolution, [status(thm)], [c_6, c_175])).
% 2.23/1.31  tff(c_190, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_41, c_182])).
% 2.23/1.31  tff(c_110, plain, (![B_56, A_55, C_57]: (~v1_xboole_0(B_56) | ~r2_hidden(A_55, k10_relat_1(C_57, B_56)) | ~v1_relat_1(C_57))), inference(resolution, [status(thm)], [c_106, c_2])).
% 2.23/1.31  tff(c_200, plain, (![A_55]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_55, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_190, c_110])).
% 2.23/1.31  tff(c_208, plain, (![A_55]: (~r2_hidden(A_55, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_6, c_200])).
% 2.23/1.31  tff(c_329, plain, (![A_77, B_78]: (~r2_hidden(A_77, k10_relat_1(k1_xboole_0, B_78)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_321, c_208])).
% 2.23/1.31  tff(c_343, plain, (![A_80, B_81]: (~r2_hidden(A_80, k10_relat_1(k1_xboole_0, B_81)))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_329])).
% 2.23/1.31  tff(c_391, plain, (![B_82]: (v1_xboole_0(k10_relat_1(k1_xboole_0, B_82)))), inference(resolution, [status(thm)], [c_4, c_343])).
% 2.23/1.31  tff(c_405, plain, (![B_82]: (k10_relat_1(k1_xboole_0, B_82)=k1_xboole_0)), inference(resolution, [status(thm)], [c_391, c_70])).
% 2.23/1.31  tff(c_30, plain, (k10_relat_1(k1_xboole_0, '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.23/1.31  tff(c_425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_405, c_30])).
% 2.23/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.31  
% 2.23/1.31  Inference rules
% 2.23/1.31  ----------------------
% 2.23/1.31  #Ref     : 0
% 2.23/1.31  #Sup     : 81
% 2.23/1.31  #Fact    : 0
% 2.23/1.31  #Define  : 0
% 2.23/1.31  #Split   : 0
% 2.23/1.31  #Chain   : 0
% 2.23/1.31  #Close   : 0
% 2.23/1.31  
% 2.23/1.31  Ordering : KBO
% 2.23/1.31  
% 2.23/1.31  Simplification rules
% 2.23/1.31  ----------------------
% 2.23/1.31  #Subsume      : 15
% 2.23/1.31  #Demod        : 23
% 2.23/1.31  #Tautology    : 18
% 2.23/1.31  #SimpNegUnit  : 0
% 2.23/1.31  #BackRed      : 4
% 2.23/1.31  
% 2.23/1.31  #Partial instantiations: 0
% 2.23/1.31  #Strategies tried      : 1
% 2.23/1.31  
% 2.23/1.31  Timing (in seconds)
% 2.23/1.31  ----------------------
% 2.23/1.32  Preprocessing        : 0.27
% 2.23/1.32  Parsing              : 0.15
% 2.23/1.32  CNF conversion       : 0.02
% 2.23/1.32  Main loop            : 0.27
% 2.23/1.32  Inferencing          : 0.12
% 2.23/1.32  Reduction            : 0.07
% 2.23/1.32  Demodulation         : 0.05
% 2.23/1.32  BG Simplification    : 0.01
% 2.23/1.32  Subsumption          : 0.06
% 2.23/1.32  Abstraction          : 0.01
% 2.23/1.32  MUC search           : 0.00
% 2.23/1.32  Cooper               : 0.00
% 2.23/1.32  Total                : 0.58
% 2.23/1.32  Index Insertion      : 0.00
% 2.23/1.32  Index Deletion       : 0.00
% 2.23/1.32  Index Matching       : 0.00
% 2.23/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
