%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:56 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   49 (  64 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   56 (  92 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,B)
          | r1_xboole_0(C,D) )
       => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C,D,E] :
      ~ ( r2_hidden(A,k3_xboole_0(k2_zfmisc_1(B,C),k2_zfmisc_1(D,E)))
        & ! [F,G] :
            ~ ( A = k4_tarski(F,G)
              & r2_hidden(F,k3_xboole_0(B,D))
              & r2_hidden(G,k3_xboole_0(C,E)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_zfmisc_1)).

tff(c_12,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_155,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r1_xboole_0(A_55,B_56)
      | ~ r2_hidden(C_57,k3_xboole_0(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_158,plain,(
    ! [A_8,C_57] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_57,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_155])).

tff(c_160,plain,(
    ! [C_57] : ~ r2_hidden(C_57,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_158])).

tff(c_55,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ r1_xboole_0(A_23,B_24)
      | ~ r2_hidden(C_25,k3_xboole_0(A_23,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_61,plain,(
    ! [A_8,C_25] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_25,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_55])).

tff(c_65,plain,(
    ! [C_25] : ~ r2_hidden(C_25,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_61])).

tff(c_22,plain,
    ( r1_xboole_0('#skF_6','#skF_7')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_31,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_37,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_31,c_37])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_82,plain,(
    ! [A_31,C_33,E_30,B_29,D_32] :
      ( r2_hidden('#skF_2'(B_29,E_30,A_31,D_32,C_33),k3_xboole_0(B_29,D_32))
      | ~ r2_hidden(A_31,k3_xboole_0(k2_zfmisc_1(B_29,C_33),k2_zfmisc_1(D_32,E_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_97,plain,(
    ! [B_44,E_45,C_46,D_47] :
      ( r2_hidden('#skF_2'(B_44,E_45,'#skF_1'(k2_zfmisc_1(B_44,C_46),k2_zfmisc_1(D_47,E_45)),D_47,C_46),k3_xboole_0(B_44,D_47))
      | r1_xboole_0(k2_zfmisc_1(B_44,C_46),k2_zfmisc_1(D_47,E_45)) ) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_112,plain,(
    ! [E_45,C_46] :
      ( r2_hidden('#skF_2'('#skF_4',E_45,'#skF_1'(k2_zfmisc_1('#skF_4',C_46),k2_zfmisc_1('#skF_5',E_45)),'#skF_5',C_46),k1_xboole_0)
      | r1_xboole_0(k2_zfmisc_1('#skF_4',C_46),k2_zfmisc_1('#skF_5',E_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_97])).

tff(c_120,plain,(
    ! [C_46,E_45] : r1_xboole_0(k2_zfmisc_1('#skF_4',C_46),k2_zfmisc_1('#skF_5',E_45)) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_112])).

tff(c_20,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_4','#skF_6'),k2_zfmisc_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_20])).

tff(c_130,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_141,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = k1_xboole_0
      | ~ r1_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_152,plain,(
    k3_xboole_0('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_130,c_141])).

tff(c_186,plain,(
    ! [E_62,C_65,D_64,A_63,B_61] :
      ( r2_hidden('#skF_3'(B_61,E_62,A_63,D_64,C_65),k3_xboole_0(C_65,E_62))
      | ~ r2_hidden(A_63,k3_xboole_0(k2_zfmisc_1(B_61,C_65),k2_zfmisc_1(D_64,E_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_231,plain,(
    ! [B_82,E_83,C_84,D_85] :
      ( r2_hidden('#skF_3'(B_82,E_83,'#skF_1'(k2_zfmisc_1(B_82,C_84),k2_zfmisc_1(D_85,E_83)),D_85,C_84),k3_xboole_0(C_84,E_83))
      | r1_xboole_0(k2_zfmisc_1(B_82,C_84),k2_zfmisc_1(D_85,E_83)) ) ),
    inference(resolution,[status(thm)],[c_6,c_186])).

tff(c_246,plain,(
    ! [B_82,D_85] :
      ( r2_hidden('#skF_3'(B_82,'#skF_7','#skF_1'(k2_zfmisc_1(B_82,'#skF_6'),k2_zfmisc_1(D_85,'#skF_7')),D_85,'#skF_6'),k1_xboole_0)
      | r1_xboole_0(k2_zfmisc_1(B_82,'#skF_6'),k2_zfmisc_1(D_85,'#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_231])).

tff(c_254,plain,(
    ! [B_82,D_85] : r1_xboole_0(k2_zfmisc_1(B_82,'#skF_6'),k2_zfmisc_1(D_85,'#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_246])).

tff(c_263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:53:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.22  
% 1.99/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.22  %$ r2_hidden > r1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 1.99/1.22  
% 1.99/1.22  %Foreground sorts:
% 1.99/1.22  
% 1.99/1.22  
% 1.99/1.22  %Background operators:
% 1.99/1.22  
% 1.99/1.22  
% 1.99/1.22  %Foreground operators:
% 1.99/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 1.99/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.99/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.22  tff('#skF_7', type, '#skF_7': $i).
% 1.99/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.99/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.99/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 1.99/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.99/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.22  
% 2.12/1.23  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.12/1.23  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.12/1.23  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.12/1.23  tff(f_65, negated_conjecture, ~(![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.12/1.23  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.12/1.23  tff(f_58, axiom, (![A, B, C, D, E]: ~(r2_hidden(A, k3_xboole_0(k2_zfmisc_1(B, C), k2_zfmisc_1(D, E))) & (![F, G]: ~(((A = k4_tarski(F, G)) & r2_hidden(F, k3_xboole_0(B, D))) & r2_hidden(G, k3_xboole_0(C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_zfmisc_1)).
% 2.12/1.23  tff(c_12, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.12/1.23  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.12/1.23  tff(c_155, plain, (![A_55, B_56, C_57]: (~r1_xboole_0(A_55, B_56) | ~r2_hidden(C_57, k3_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.23  tff(c_158, plain, (![A_8, C_57]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_57, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_155])).
% 2.12/1.23  tff(c_160, plain, (![C_57]: (~r2_hidden(C_57, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_158])).
% 2.12/1.23  tff(c_55, plain, (![A_23, B_24, C_25]: (~r1_xboole_0(A_23, B_24) | ~r2_hidden(C_25, k3_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.23  tff(c_61, plain, (![A_8, C_25]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_25, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_55])).
% 2.12/1.23  tff(c_65, plain, (![C_25]: (~r2_hidden(C_25, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_61])).
% 2.12/1.23  tff(c_22, plain, (r1_xboole_0('#skF_6', '#skF_7') | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.12/1.23  tff(c_31, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_22])).
% 2.12/1.23  tff(c_37, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.23  tff(c_48, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_31, c_37])).
% 2.12/1.23  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.23  tff(c_82, plain, (![A_31, C_33, E_30, B_29, D_32]: (r2_hidden('#skF_2'(B_29, E_30, A_31, D_32, C_33), k3_xboole_0(B_29, D_32)) | ~r2_hidden(A_31, k3_xboole_0(k2_zfmisc_1(B_29, C_33), k2_zfmisc_1(D_32, E_30))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.23  tff(c_97, plain, (![B_44, E_45, C_46, D_47]: (r2_hidden('#skF_2'(B_44, E_45, '#skF_1'(k2_zfmisc_1(B_44, C_46), k2_zfmisc_1(D_47, E_45)), D_47, C_46), k3_xboole_0(B_44, D_47)) | r1_xboole_0(k2_zfmisc_1(B_44, C_46), k2_zfmisc_1(D_47, E_45)))), inference(resolution, [status(thm)], [c_6, c_82])).
% 2.12/1.23  tff(c_112, plain, (![E_45, C_46]: (r2_hidden('#skF_2'('#skF_4', E_45, '#skF_1'(k2_zfmisc_1('#skF_4', C_46), k2_zfmisc_1('#skF_5', E_45)), '#skF_5', C_46), k1_xboole_0) | r1_xboole_0(k2_zfmisc_1('#skF_4', C_46), k2_zfmisc_1('#skF_5', E_45)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_97])).
% 2.12/1.23  tff(c_120, plain, (![C_46, E_45]: (r1_xboole_0(k2_zfmisc_1('#skF_4', C_46), k2_zfmisc_1('#skF_5', E_45)))), inference(negUnitSimplification, [status(thm)], [c_65, c_112])).
% 2.12/1.23  tff(c_20, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_6'), k2_zfmisc_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.12/1.23  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_20])).
% 2.12/1.23  tff(c_130, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_22])).
% 2.12/1.23  tff(c_141, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=k1_xboole_0 | ~r1_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.23  tff(c_152, plain, (k3_xboole_0('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_130, c_141])).
% 2.12/1.23  tff(c_186, plain, (![E_62, C_65, D_64, A_63, B_61]: (r2_hidden('#skF_3'(B_61, E_62, A_63, D_64, C_65), k3_xboole_0(C_65, E_62)) | ~r2_hidden(A_63, k3_xboole_0(k2_zfmisc_1(B_61, C_65), k2_zfmisc_1(D_64, E_62))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.23  tff(c_231, plain, (![B_82, E_83, C_84, D_85]: (r2_hidden('#skF_3'(B_82, E_83, '#skF_1'(k2_zfmisc_1(B_82, C_84), k2_zfmisc_1(D_85, E_83)), D_85, C_84), k3_xboole_0(C_84, E_83)) | r1_xboole_0(k2_zfmisc_1(B_82, C_84), k2_zfmisc_1(D_85, E_83)))), inference(resolution, [status(thm)], [c_6, c_186])).
% 2.12/1.23  tff(c_246, plain, (![B_82, D_85]: (r2_hidden('#skF_3'(B_82, '#skF_7', '#skF_1'(k2_zfmisc_1(B_82, '#skF_6'), k2_zfmisc_1(D_85, '#skF_7')), D_85, '#skF_6'), k1_xboole_0) | r1_xboole_0(k2_zfmisc_1(B_82, '#skF_6'), k2_zfmisc_1(D_85, '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_152, c_231])).
% 2.12/1.23  tff(c_254, plain, (![B_82, D_85]: (r1_xboole_0(k2_zfmisc_1(B_82, '#skF_6'), k2_zfmisc_1(D_85, '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_160, c_246])).
% 2.12/1.23  tff(c_263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_254, c_20])).
% 2.12/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.23  
% 2.12/1.23  Inference rules
% 2.12/1.23  ----------------------
% 2.12/1.23  #Ref     : 0
% 2.12/1.23  #Sup     : 52
% 2.12/1.23  #Fact    : 0
% 2.12/1.23  #Define  : 0
% 2.12/1.23  #Split   : 1
% 2.12/1.23  #Chain   : 0
% 2.12/1.23  #Close   : 0
% 2.12/1.23  
% 2.12/1.23  Ordering : KBO
% 2.12/1.23  
% 2.12/1.23  Simplification rules
% 2.12/1.23  ----------------------
% 2.12/1.23  #Subsume      : 2
% 2.12/1.23  #Demod        : 12
% 2.12/1.23  #Tautology    : 16
% 2.12/1.23  #SimpNegUnit  : 10
% 2.12/1.23  #BackRed      : 2
% 2.12/1.23  
% 2.12/1.23  #Partial instantiations: 0
% 2.12/1.23  #Strategies tried      : 1
% 2.12/1.23  
% 2.12/1.23  Timing (in seconds)
% 2.12/1.23  ----------------------
% 2.13/1.23  Preprocessing        : 0.27
% 2.13/1.23  Parsing              : 0.15
% 2.13/1.23  CNF conversion       : 0.02
% 2.13/1.24  Main loop            : 0.22
% 2.13/1.24  Inferencing          : 0.09
% 2.13/1.24  Reduction            : 0.06
% 2.13/1.24  Demodulation         : 0.04
% 2.13/1.24  BG Simplification    : 0.01
% 2.13/1.24  Subsumption          : 0.03
% 2.13/1.24  Abstraction          : 0.02
% 2.13/1.24  MUC search           : 0.00
% 2.13/1.24  Cooper               : 0.00
% 2.13/1.24  Total                : 0.51
% 2.13/1.24  Index Insertion      : 0.00
% 2.13/1.24  Index Deletion       : 0.00
% 2.13/1.24  Index Matching       : 0.00
% 2.13/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
