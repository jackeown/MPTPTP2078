%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:35 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :   60 (  77 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 124 expanded)
%              Number of equality atoms :   35 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_84,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_22,plain,(
    ! [B_12] : r1_tarski(k1_xboole_0,k1_tarski(B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_131,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_144,plain,(
    ! [B_12] : k4_xboole_0(k1_xboole_0,k1_tarski(B_12)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_131])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_100,plain,(
    ! [A_37,B_38] : r1_xboole_0(k4_xboole_0(A_37,B_38),k4_xboole_0(B_38,A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_5] :
      ( ~ r1_xboole_0(A_5,A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_111,plain,(
    ! [B_38] : k4_xboole_0(B_38,B_38) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_100,c_10])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(k1_tarski(A_9),B_10)
      | r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_213,plain,(
    ! [A_56,B_57] :
      ( k7_relat_1(A_56,B_57) = k1_xboole_0
      | ~ r1_xboole_0(B_57,k1_relat_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_221,plain,(
    ! [A_56,A_9] :
      ( k7_relat_1(A_56,k1_tarski(A_9)) = k1_xboole_0
      | ~ v1_relat_1(A_56)
      | r2_hidden(A_9,k1_relat_1(A_56)) ) ),
    inference(resolution,[status(thm)],[c_16,c_213])).

tff(c_14,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_374,plain,(
    ! [C_72,A_73,B_74] :
      ( k2_tarski(k1_funct_1(C_72,A_73),k1_funct_1(C_72,B_74)) = k9_relat_1(C_72,k2_tarski(A_73,B_74))
      | ~ r2_hidden(B_74,k1_relat_1(C_72))
      | ~ r2_hidden(A_73,k1_relat_1(C_72))
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_388,plain,(
    ! [C_72,A_73] :
      ( k9_relat_1(C_72,k2_tarski(A_73,A_73)) = k1_tarski(k1_funct_1(C_72,A_73))
      | ~ r2_hidden(A_73,k1_relat_1(C_72))
      | ~ r2_hidden(A_73,k1_relat_1(C_72))
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_374])).

tff(c_762,plain,(
    ! [C_104,A_105] :
      ( k9_relat_1(C_104,k1_tarski(A_105)) = k1_tarski(k1_funct_1(C_104,A_105))
      | ~ r2_hidden(A_105,k1_relat_1(C_104))
      | ~ r2_hidden(A_105,k1_relat_1(C_104))
      | ~ v1_funct_1(C_104)
      | ~ v1_relat_1(C_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_388])).

tff(c_1703,plain,(
    ! [A_141,A_142] :
      ( k9_relat_1(A_141,k1_tarski(A_142)) = k1_tarski(k1_funct_1(A_141,A_142))
      | ~ r2_hidden(A_142,k1_relat_1(A_141))
      | ~ v1_funct_1(A_141)
      | k7_relat_1(A_141,k1_tarski(A_142)) = k1_xboole_0
      | ~ v1_relat_1(A_141) ) ),
    inference(resolution,[status(thm)],[c_221,c_762])).

tff(c_1781,plain,(
    ! [A_145,A_146] :
      ( k9_relat_1(A_145,k1_tarski(A_146)) = k1_tarski(k1_funct_1(A_145,A_146))
      | ~ v1_funct_1(A_145)
      | k7_relat_1(A_145,k1_tarski(A_146)) = k1_xboole_0
      | ~ v1_relat_1(A_145) ) ),
    inference(resolution,[status(thm)],[c_221,c_1703])).

tff(c_171,plain,(
    ! [B_47,A_48] :
      ( k2_relat_1(k7_relat_1(B_47,A_48)) = k9_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_95,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | k4_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_99,plain,(
    k4_xboole_0(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_42])).

tff(c_177,plain,
    ( k4_xboole_0(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_99])).

tff(c_186,plain,(
    k4_xboole_0(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_177])).

tff(c_1822,plain,
    ( k4_xboole_0(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) != k1_xboole_0
    | ~ v1_funct_1('#skF_2')
    | k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1781,c_186])).

tff(c_1844,plain,(
    k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_111,c_1822])).

tff(c_1850,plain,(
    k4_xboole_0(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1844,c_99])).

tff(c_1854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_36,c_1850])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 14:53:25 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.64  
% 3.72/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.72/1.64  
% 3.72/1.64  %Foreground sorts:
% 3.72/1.64  
% 3.72/1.64  
% 3.72/1.64  %Background operators:
% 3.72/1.64  
% 3.72/1.64  
% 3.72/1.64  %Foreground operators:
% 3.72/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.72/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.72/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.72/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.72/1.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.72/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.72/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.72/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.72/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.72/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.72/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.72/1.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.72/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.72/1.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.72/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.64  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.72/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.72/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.72/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.72/1.64  
% 3.72/1.66  tff(f_58, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.72/1.66  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.72/1.66  tff(f_84, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.72/1.66  tff(f_101, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_funct_1)).
% 3.72/1.66  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_xboole_1)).
% 3.72/1.66  tff(f_43, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.72/1.66  tff(f_52, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.72/1.66  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 3.72/1.66  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.72/1.66  tff(f_94, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 3.72/1.66  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.72/1.66  tff(c_22, plain, (![B_12]: (r1_tarski(k1_xboole_0, k1_tarski(B_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.72/1.66  tff(c_131, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.72/1.66  tff(c_144, plain, (![B_12]: (k4_xboole_0(k1_xboole_0, k1_tarski(B_12))=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_131])).
% 3.72/1.66  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.72/1.66  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.72/1.66  tff(c_44, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.72/1.66  tff(c_100, plain, (![A_37, B_38]: (r1_xboole_0(k4_xboole_0(A_37, B_38), k4_xboole_0(B_38, A_37)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.72/1.66  tff(c_10, plain, (![A_5]: (~r1_xboole_0(A_5, A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.72/1.66  tff(c_111, plain, (![B_38]: (k4_xboole_0(B_38, B_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_100, c_10])).
% 3.72/1.66  tff(c_16, plain, (![A_9, B_10]: (r1_xboole_0(k1_tarski(A_9), B_10) | r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.72/1.66  tff(c_213, plain, (![A_56, B_57]: (k7_relat_1(A_56, B_57)=k1_xboole_0 | ~r1_xboole_0(B_57, k1_relat_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.72/1.66  tff(c_221, plain, (![A_56, A_9]: (k7_relat_1(A_56, k1_tarski(A_9))=k1_xboole_0 | ~v1_relat_1(A_56) | r2_hidden(A_9, k1_relat_1(A_56)))), inference(resolution, [status(thm)], [c_16, c_213])).
% 3.72/1.66  tff(c_14, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.72/1.66  tff(c_374, plain, (![C_72, A_73, B_74]: (k2_tarski(k1_funct_1(C_72, A_73), k1_funct_1(C_72, B_74))=k9_relat_1(C_72, k2_tarski(A_73, B_74)) | ~r2_hidden(B_74, k1_relat_1(C_72)) | ~r2_hidden(A_73, k1_relat_1(C_72)) | ~v1_funct_1(C_72) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.72/1.66  tff(c_388, plain, (![C_72, A_73]: (k9_relat_1(C_72, k2_tarski(A_73, A_73))=k1_tarski(k1_funct_1(C_72, A_73)) | ~r2_hidden(A_73, k1_relat_1(C_72)) | ~r2_hidden(A_73, k1_relat_1(C_72)) | ~v1_funct_1(C_72) | ~v1_relat_1(C_72))), inference(superposition, [status(thm), theory('equality')], [c_14, c_374])).
% 3.72/1.66  tff(c_762, plain, (![C_104, A_105]: (k9_relat_1(C_104, k1_tarski(A_105))=k1_tarski(k1_funct_1(C_104, A_105)) | ~r2_hidden(A_105, k1_relat_1(C_104)) | ~r2_hidden(A_105, k1_relat_1(C_104)) | ~v1_funct_1(C_104) | ~v1_relat_1(C_104))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_388])).
% 3.72/1.66  tff(c_1703, plain, (![A_141, A_142]: (k9_relat_1(A_141, k1_tarski(A_142))=k1_tarski(k1_funct_1(A_141, A_142)) | ~r2_hidden(A_142, k1_relat_1(A_141)) | ~v1_funct_1(A_141) | k7_relat_1(A_141, k1_tarski(A_142))=k1_xboole_0 | ~v1_relat_1(A_141))), inference(resolution, [status(thm)], [c_221, c_762])).
% 3.72/1.66  tff(c_1781, plain, (![A_145, A_146]: (k9_relat_1(A_145, k1_tarski(A_146))=k1_tarski(k1_funct_1(A_145, A_146)) | ~v1_funct_1(A_145) | k7_relat_1(A_145, k1_tarski(A_146))=k1_xboole_0 | ~v1_relat_1(A_145))), inference(resolution, [status(thm)], [c_221, c_1703])).
% 3.72/1.66  tff(c_171, plain, (![B_47, A_48]: (k2_relat_1(k7_relat_1(B_47, A_48))=k9_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.72/1.66  tff(c_95, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | k4_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.72/1.66  tff(c_42, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.72/1.66  tff(c_99, plain, (k4_xboole_0(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_42])).
% 3.72/1.66  tff(c_177, plain, (k4_xboole_0(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_171, c_99])).
% 3.72/1.66  tff(c_186, plain, (k4_xboole_0(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_177])).
% 3.72/1.66  tff(c_1822, plain, (k4_xboole_0(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))!=k1_xboole_0 | ~v1_funct_1('#skF_2') | k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1781, c_186])).
% 3.72/1.66  tff(c_1844, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_111, c_1822])).
% 3.72/1.66  tff(c_1850, plain, (k4_xboole_0(k2_relat_1(k1_xboole_0), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1844, c_99])).
% 3.72/1.66  tff(c_1854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_36, c_1850])).
% 3.72/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.66  
% 3.72/1.66  Inference rules
% 3.72/1.66  ----------------------
% 3.72/1.66  #Ref     : 0
% 3.72/1.66  #Sup     : 394
% 3.72/1.66  #Fact    : 0
% 3.72/1.66  #Define  : 0
% 3.72/1.66  #Split   : 2
% 3.72/1.66  #Chain   : 0
% 3.72/1.66  #Close   : 0
% 3.72/1.66  
% 3.72/1.66  Ordering : KBO
% 3.72/1.66  
% 3.72/1.66  Simplification rules
% 3.72/1.66  ----------------------
% 3.72/1.66  #Subsume      : 80
% 3.72/1.66  #Demod        : 589
% 3.72/1.66  #Tautology    : 211
% 3.72/1.66  #SimpNegUnit  : 2
% 3.72/1.66  #BackRed      : 3
% 3.72/1.66  
% 3.72/1.66  #Partial instantiations: 0
% 3.72/1.66  #Strategies tried      : 1
% 3.72/1.66  
% 3.72/1.66  Timing (in seconds)
% 3.72/1.66  ----------------------
% 3.72/1.66  Preprocessing        : 0.32
% 3.72/1.66  Parsing              : 0.17
% 3.72/1.66  CNF conversion       : 0.02
% 3.72/1.66  Main loop            : 0.56
% 3.72/1.66  Inferencing          : 0.20
% 3.72/1.66  Reduction            : 0.20
% 3.72/1.66  Demodulation         : 0.15
% 3.72/1.66  BG Simplification    : 0.02
% 3.72/1.66  Subsumption          : 0.10
% 3.72/1.66  Abstraction          : 0.03
% 3.72/1.66  MUC search           : 0.00
% 3.72/1.66  Cooper               : 0.00
% 3.72/1.66  Total                : 0.91
% 3.72/1.66  Index Insertion      : 0.00
% 3.72/1.66  Index Deletion       : 0.00
% 3.72/1.66  Index Matching       : 0.00
% 3.72/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
