%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:25 EST 2020

% Result     : Theorem 5.81s
% Output     : CNFRefutation 5.81s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 112 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  102 ( 329 expanded)
%              Number of equality atoms :    8 (  28 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(c_40,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,(
    v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_70,plain,(
    ! [C_67,A_68,B_69] :
      ( k3_xboole_0(k9_relat_1(C_67,A_68),k9_relat_1(C_67,B_69)) = k9_relat_1(C_67,k3_xboole_0(A_68,B_69))
      | ~ v2_funct_1(C_67)
      | ~ v1_funct_1(C_67)
      | ~ v1_relat_1(C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2856,plain,(
    ! [C_239,A_240,B_241] :
      ( r2_hidden('#skF_1'(k9_relat_1(C_239,A_240),k9_relat_1(C_239,B_241)),k9_relat_1(C_239,k3_xboole_0(A_240,B_241)))
      | r1_xboole_0(k9_relat_1(C_239,A_240),k9_relat_1(C_239,B_241))
      | ~ v2_funct_1(C_239)
      | ~ v1_funct_1(C_239)
      | ~ v1_relat_1(C_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2])).

tff(c_14,plain,(
    ! [A_10,B_33,D_48] :
      ( r2_hidden('#skF_5'(A_10,B_33,k9_relat_1(A_10,B_33),D_48),B_33)
      | ~ r2_hidden(D_48,k9_relat_1(A_10,B_33))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_118,plain,(
    ! [A_83,B_84,C_85] :
      ( r2_hidden('#skF_3'(A_83,B_84,C_85),B_84)
      | r2_hidden('#skF_4'(A_83,B_84,C_85),C_85)
      | k9_relat_1(A_83,B_84) = C_85
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_196,plain,(
    ! [A_101,B_102,A_103,C_104] :
      ( ~ r1_xboole_0(A_101,B_102)
      | r2_hidden('#skF_4'(A_103,k3_xboole_0(A_101,B_102),C_104),C_104)
      | k9_relat_1(A_103,k3_xboole_0(A_101,B_102)) = C_104
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(resolution,[status(thm)],[c_118,c_4])).

tff(c_215,plain,(
    ! [B_107,A_109,A_105,A_106,B_108] :
      ( ~ r1_xboole_0(A_109,B_108)
      | ~ r1_xboole_0(A_105,B_107)
      | k9_relat_1(A_106,k3_xboole_0(A_105,B_107)) = k3_xboole_0(A_109,B_108)
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(resolution,[status(thm)],[c_196,c_4])).

tff(c_219,plain,(
    ! [A_110,B_111,A_112] :
      ( ~ r1_xboole_0(A_110,B_111)
      | k9_relat_1(A_112,k3_xboole_0(A_110,B_111)) = k3_xboole_0('#skF_6','#skF_7')
      | ~ v1_funct_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(resolution,[status(thm)],[c_40,c_215])).

tff(c_85,plain,(
    ! [A_70,B_71,D_72] :
      ( r2_hidden('#skF_5'(A_70,B_71,k9_relat_1(A_70,B_71),D_72),B_71)
      | ~ r2_hidden(D_72,k9_relat_1(A_70,B_71))
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_90,plain,(
    ! [A_1,B_2,D_72,A_70] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(D_72,k9_relat_1(A_70,k3_xboole_0(A_1,B_2)))
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(resolution,[status(thm)],[c_85,c_4])).

tff(c_238,plain,(
    ! [A_110,B_111,D_72,A_112] :
      ( ~ r1_xboole_0(A_110,B_111)
      | ~ r2_hidden(D_72,k3_xboole_0('#skF_6','#skF_7'))
      | ~ v1_funct_1(A_112)
      | ~ v1_relat_1(A_112)
      | ~ r1_xboole_0(A_110,B_111)
      | ~ v1_funct_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_90])).

tff(c_260,plain,(
    ! [A_113] :
      ( ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113)
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(splitLeft,[status(thm)],[c_238])).

tff(c_262,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_260])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_262])).

tff(c_267,plain,(
    ! [A_110,B_111,D_72] :
      ( ~ r1_xboole_0(A_110,B_111)
      | ~ r1_xboole_0(A_110,B_111)
      | ~ r2_hidden(D_72,k3_xboole_0('#skF_6','#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_238])).

tff(c_296,plain,(
    ! [D_117] : ~ r2_hidden(D_117,k3_xboole_0('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_335,plain,(
    ! [D_48,A_10] :
      ( ~ r2_hidden(D_48,k9_relat_1(A_10,k3_xboole_0('#skF_6','#skF_7')))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_296])).

tff(c_3017,plain,(
    ! [C_242] :
      ( r1_xboole_0(k9_relat_1(C_242,'#skF_6'),k9_relat_1(C_242,'#skF_7'))
      | ~ v2_funct_1(C_242)
      | ~ v1_funct_1(C_242)
      | ~ v1_relat_1(C_242) ) ),
    inference(resolution,[status(thm)],[c_2856,c_335])).

tff(c_36,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_8','#skF_6'),k9_relat_1('#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3034,plain,
    ( ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_3017,c_36])).

tff(c_3045,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_3034])).

tff(c_3047,plain,(
    ! [A_243,B_244] :
      ( ~ r1_xboole_0(A_243,B_244)
      | ~ r1_xboole_0(A_243,B_244) ) ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_3049,plain,(
    ~ r1_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_3047])).

tff(c_3053,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3049])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:29:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.81/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.12  
% 5.81/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.13  %$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 5.81/2.13  
% 5.81/2.13  %Foreground sorts:
% 5.81/2.13  
% 5.81/2.13  
% 5.81/2.13  %Background operators:
% 5.81/2.13  
% 5.81/2.13  
% 5.81/2.13  %Foreground operators:
% 5.81/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.81/2.13  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.81/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.81/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.81/2.13  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.81/2.13  tff('#skF_7', type, '#skF_7': $i).
% 5.81/2.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.81/2.13  tff('#skF_6', type, '#skF_6': $i).
% 5.81/2.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.81/2.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.81/2.13  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.81/2.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.81/2.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.81/2.13  tff('#skF_8', type, '#skF_8': $i).
% 5.81/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.81/2.13  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 5.81/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.81/2.13  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.81/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.81/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.81/2.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.81/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.81/2.13  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.81/2.13  
% 5.81/2.14  tff(f_79, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_funct_1)).
% 5.81/2.14  tff(f_68, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_1)).
% 5.81/2.14  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.81/2.14  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 5.81/2.14  tff(c_40, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.81/2.14  tff(c_44, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.81/2.14  tff(c_42, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.81/2.14  tff(c_38, plain, (v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.81/2.14  tff(c_70, plain, (![C_67, A_68, B_69]: (k3_xboole_0(k9_relat_1(C_67, A_68), k9_relat_1(C_67, B_69))=k9_relat_1(C_67, k3_xboole_0(A_68, B_69)) | ~v2_funct_1(C_67) | ~v1_funct_1(C_67) | ~v1_relat_1(C_67))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.81/2.14  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), k3_xboole_0(A_1, B_2)) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.81/2.14  tff(c_2856, plain, (![C_239, A_240, B_241]: (r2_hidden('#skF_1'(k9_relat_1(C_239, A_240), k9_relat_1(C_239, B_241)), k9_relat_1(C_239, k3_xboole_0(A_240, B_241))) | r1_xboole_0(k9_relat_1(C_239, A_240), k9_relat_1(C_239, B_241)) | ~v2_funct_1(C_239) | ~v1_funct_1(C_239) | ~v1_relat_1(C_239))), inference(superposition, [status(thm), theory('equality')], [c_70, c_2])).
% 5.81/2.14  tff(c_14, plain, (![A_10, B_33, D_48]: (r2_hidden('#skF_5'(A_10, B_33, k9_relat_1(A_10, B_33), D_48), B_33) | ~r2_hidden(D_48, k9_relat_1(A_10, B_33)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.81/2.14  tff(c_118, plain, (![A_83, B_84, C_85]: (r2_hidden('#skF_3'(A_83, B_84, C_85), B_84) | r2_hidden('#skF_4'(A_83, B_84, C_85), C_85) | k9_relat_1(A_83, B_84)=C_85 | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.81/2.14  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.81/2.14  tff(c_196, plain, (![A_101, B_102, A_103, C_104]: (~r1_xboole_0(A_101, B_102) | r2_hidden('#skF_4'(A_103, k3_xboole_0(A_101, B_102), C_104), C_104) | k9_relat_1(A_103, k3_xboole_0(A_101, B_102))=C_104 | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(resolution, [status(thm)], [c_118, c_4])).
% 5.81/2.14  tff(c_215, plain, (![B_107, A_109, A_105, A_106, B_108]: (~r1_xboole_0(A_109, B_108) | ~r1_xboole_0(A_105, B_107) | k9_relat_1(A_106, k3_xboole_0(A_105, B_107))=k3_xboole_0(A_109, B_108) | ~v1_funct_1(A_106) | ~v1_relat_1(A_106))), inference(resolution, [status(thm)], [c_196, c_4])).
% 5.81/2.14  tff(c_219, plain, (![A_110, B_111, A_112]: (~r1_xboole_0(A_110, B_111) | k9_relat_1(A_112, k3_xboole_0(A_110, B_111))=k3_xboole_0('#skF_6', '#skF_7') | ~v1_funct_1(A_112) | ~v1_relat_1(A_112))), inference(resolution, [status(thm)], [c_40, c_215])).
% 5.81/2.14  tff(c_85, plain, (![A_70, B_71, D_72]: (r2_hidden('#skF_5'(A_70, B_71, k9_relat_1(A_70, B_71), D_72), B_71) | ~r2_hidden(D_72, k9_relat_1(A_70, B_71)) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.81/2.14  tff(c_90, plain, (![A_1, B_2, D_72, A_70]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(D_72, k9_relat_1(A_70, k3_xboole_0(A_1, B_2))) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(resolution, [status(thm)], [c_85, c_4])).
% 5.81/2.14  tff(c_238, plain, (![A_110, B_111, D_72, A_112]: (~r1_xboole_0(A_110, B_111) | ~r2_hidden(D_72, k3_xboole_0('#skF_6', '#skF_7')) | ~v1_funct_1(A_112) | ~v1_relat_1(A_112) | ~r1_xboole_0(A_110, B_111) | ~v1_funct_1(A_112) | ~v1_relat_1(A_112))), inference(superposition, [status(thm), theory('equality')], [c_219, c_90])).
% 5.81/2.14  tff(c_260, plain, (![A_113]: (~v1_funct_1(A_113) | ~v1_relat_1(A_113) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(splitLeft, [status(thm)], [c_238])).
% 5.81/2.14  tff(c_262, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_44, c_260])).
% 5.81/2.14  tff(c_266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_262])).
% 5.81/2.14  tff(c_267, plain, (![A_110, B_111, D_72]: (~r1_xboole_0(A_110, B_111) | ~r1_xboole_0(A_110, B_111) | ~r2_hidden(D_72, k3_xboole_0('#skF_6', '#skF_7')))), inference(splitRight, [status(thm)], [c_238])).
% 5.81/2.14  tff(c_296, plain, (![D_117]: (~r2_hidden(D_117, k3_xboole_0('#skF_6', '#skF_7')))), inference(splitLeft, [status(thm)], [c_267])).
% 5.81/2.14  tff(c_335, plain, (![D_48, A_10]: (~r2_hidden(D_48, k9_relat_1(A_10, k3_xboole_0('#skF_6', '#skF_7'))) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_14, c_296])).
% 5.81/2.14  tff(c_3017, plain, (![C_242]: (r1_xboole_0(k9_relat_1(C_242, '#skF_6'), k9_relat_1(C_242, '#skF_7')) | ~v2_funct_1(C_242) | ~v1_funct_1(C_242) | ~v1_relat_1(C_242))), inference(resolution, [status(thm)], [c_2856, c_335])).
% 5.81/2.14  tff(c_36, plain, (~r1_xboole_0(k9_relat_1('#skF_8', '#skF_6'), k9_relat_1('#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.81/2.14  tff(c_3034, plain, (~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_3017, c_36])).
% 5.81/2.14  tff(c_3045, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_3034])).
% 5.81/2.14  tff(c_3047, plain, (![A_243, B_244]: (~r1_xboole_0(A_243, B_244) | ~r1_xboole_0(A_243, B_244))), inference(splitRight, [status(thm)], [c_267])).
% 5.81/2.14  tff(c_3049, plain, (~r1_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_40, c_3047])).
% 5.81/2.14  tff(c_3053, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_3049])).
% 5.81/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.14  
% 5.81/2.14  Inference rules
% 5.81/2.14  ----------------------
% 5.81/2.14  #Ref     : 0
% 5.81/2.14  #Sup     : 771
% 5.81/2.14  #Fact    : 0
% 5.81/2.14  #Define  : 0
% 5.81/2.14  #Split   : 5
% 5.81/2.14  #Chain   : 0
% 5.81/2.14  #Close   : 0
% 5.81/2.14  
% 5.81/2.14  Ordering : KBO
% 5.81/2.14  
% 5.81/2.14  Simplification rules
% 5.81/2.14  ----------------------
% 5.81/2.14  #Subsume      : 377
% 5.81/2.14  #Demod        : 154
% 5.81/2.14  #Tautology    : 38
% 5.81/2.14  #SimpNegUnit  : 15
% 5.81/2.14  #BackRed      : 0
% 5.81/2.14  
% 5.81/2.14  #Partial instantiations: 0
% 5.81/2.14  #Strategies tried      : 1
% 5.81/2.14  
% 5.81/2.14  Timing (in seconds)
% 5.81/2.14  ----------------------
% 5.81/2.14  Preprocessing        : 0.31
% 5.81/2.14  Parsing              : 0.16
% 5.81/2.14  CNF conversion       : 0.03
% 5.81/2.14  Main loop            : 1.09
% 5.81/2.14  Inferencing          : 0.32
% 5.81/2.14  Reduction            : 0.22
% 5.81/2.14  Demodulation         : 0.15
% 5.81/2.14  BG Simplification    : 0.04
% 5.81/2.15  Subsumption          : 0.45
% 5.81/2.15  Abstraction          : 0.06
% 5.81/2.15  MUC search           : 0.00
% 5.81/2.15  Cooper               : 0.00
% 5.81/2.15  Total                : 1.43
% 5.81/2.15  Index Insertion      : 0.00
% 5.81/2.15  Index Deletion       : 0.00
% 5.81/2.15  Index Matching       : 0.00
% 5.81/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
