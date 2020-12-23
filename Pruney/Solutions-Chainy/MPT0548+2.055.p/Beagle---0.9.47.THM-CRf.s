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
% DateTime   : Thu Dec  3 10:00:42 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   71 (  87 expanded)
%              Number of leaves         :   37 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 104 expanded)
%              Number of equality atoms :   31 (  39 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_57,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_73,axiom,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_57,plain,(
    ! [A_35] : k2_zfmisc_1(A_35,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_61,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_30])).

tff(c_106,plain,(
    ! [B_42,A_43] :
      ( r1_tarski(k7_relat_1(B_42,A_43),B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_10,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_110,plain,(
    ! [A_43] :
      ( k7_relat_1(k1_xboole_0,A_43) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_106,c_10])).

tff(c_113,plain,(
    ! [A_43] : k7_relat_1(k1_xboole_0,A_43) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_110])).

tff(c_195,plain,(
    ! [B_57,A_58] :
      ( k2_relat_1(k7_relat_1(B_57,A_58)) = k9_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_204,plain,(
    ! [A_43] :
      ( k9_relat_1(k1_xboole_0,A_43) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_195])).

tff(c_208,plain,(
    ! [A_43] : k9_relat_1(k1_xboole_0,A_43) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_204])).

tff(c_48,plain,(
    k9_relat_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_209,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_48])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_152,plain,(
    ! [A_50,B_51] :
      ( k2_xboole_0(A_50,B_51) = B_51
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_160,plain,(
    ! [A_7] : k2_xboole_0(k1_xboole_0,A_7) = A_7 ),
    inference(resolution,[status(thm)],[c_8,c_152])).

tff(c_34,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_135,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden(A_47,B_48)
      | ~ r1_xboole_0(k1_tarski(A_47),B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_140,plain,(
    ! [A_47] : ~ r2_hidden(A_47,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_135])).

tff(c_229,plain,(
    ! [B_61,A_62] :
      ( k7_relat_1(B_61,A_62) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_61),A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_235,plain,(
    ! [B_63] :
      ( k7_relat_1(B_63,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_63) ) ),
    inference(resolution,[status(thm)],[c_12,c_229])).

tff(c_244,plain,(
    ! [A_19,B_20] : k7_relat_1(k2_zfmisc_1(A_19,B_20),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_235])).

tff(c_291,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden(A_70,B_71)
      | ~ r2_hidden(A_70,k1_relat_1(k7_relat_1(C_72,B_71)))
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_294,plain,(
    ! [A_70,A_19,B_20] :
      ( r2_hidden(A_70,k1_xboole_0)
      | ~ r2_hidden(A_70,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k2_zfmisc_1(A_19,B_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_291])).

tff(c_303,plain,(
    ! [A_70] :
      ( r2_hidden(A_70,k1_xboole_0)
      | ~ r2_hidden(A_70,k1_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_294])).

tff(c_308,plain,(
    ! [A_73] : ~ r2_hidden(A_73,k1_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_303])).

tff(c_313,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_308])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_317,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_313,c_14])).

tff(c_28,plain,(
    ! [A_18] :
      ( k2_xboole_0(k1_relat_1(A_18),k2_relat_1(A_18)) = k3_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_347,plain,
    ( k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_28])).

tff(c_355,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_160,c_34,c_347])).

tff(c_357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_355])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.36  
% 2.23/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.36  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2
% 2.23/1.36  
% 2.23/1.36  %Foreground sorts:
% 2.23/1.36  
% 2.23/1.36  
% 2.23/1.36  %Background operators:
% 2.23/1.36  
% 2.23/1.36  
% 2.23/1.36  %Foreground operators:
% 2.23/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.23/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.36  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.23/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.23/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.36  
% 2.23/1.37  tff(f_57, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.23/1.37  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.23/1.37  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.23/1.37  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.23/1.37  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.23/1.37  tff(f_94, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.23/1.37  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.23/1.37  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.23/1.37  tff(f_73, axiom, (k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_relat_1)).
% 2.23/1.37  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.23/1.37  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.23/1.37  tff(f_62, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_zfmisc_1)).
% 2.23/1.37  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.23/1.37  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.23/1.37  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 2.23/1.37  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.23/1.37  tff(c_57, plain, (![A_35]: (k2_zfmisc_1(A_35, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.23/1.37  tff(c_30, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.23/1.37  tff(c_61, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_57, c_30])).
% 2.23/1.37  tff(c_106, plain, (![B_42, A_43]: (r1_tarski(k7_relat_1(B_42, A_43), B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.23/1.37  tff(c_10, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.23/1.37  tff(c_110, plain, (![A_43]: (k7_relat_1(k1_xboole_0, A_43)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_106, c_10])).
% 2.23/1.37  tff(c_113, plain, (![A_43]: (k7_relat_1(k1_xboole_0, A_43)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_110])).
% 2.23/1.37  tff(c_195, plain, (![B_57, A_58]: (k2_relat_1(k7_relat_1(B_57, A_58))=k9_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.23/1.37  tff(c_204, plain, (![A_43]: (k9_relat_1(k1_xboole_0, A_43)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_113, c_195])).
% 2.23/1.37  tff(c_208, plain, (![A_43]: (k9_relat_1(k1_xboole_0, A_43)=k2_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_204])).
% 2.23/1.37  tff(c_48, plain, (k9_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.23/1.37  tff(c_209, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_208, c_48])).
% 2.23/1.37  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.23/1.37  tff(c_152, plain, (![A_50, B_51]: (k2_xboole_0(A_50, B_51)=B_51 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.37  tff(c_160, plain, (![A_7]: (k2_xboole_0(k1_xboole_0, A_7)=A_7)), inference(resolution, [status(thm)], [c_8, c_152])).
% 2.23/1.37  tff(c_34, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.23/1.37  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.37  tff(c_12, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.23/1.37  tff(c_135, plain, (![A_47, B_48]: (~r2_hidden(A_47, B_48) | ~r1_xboole_0(k1_tarski(A_47), B_48))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.23/1.37  tff(c_140, plain, (![A_47]: (~r2_hidden(A_47, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_135])).
% 2.23/1.37  tff(c_229, plain, (![B_61, A_62]: (k7_relat_1(B_61, A_62)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_61), A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.23/1.37  tff(c_235, plain, (![B_63]: (k7_relat_1(B_63, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_63))), inference(resolution, [status(thm)], [c_12, c_229])).
% 2.23/1.37  tff(c_244, plain, (![A_19, B_20]: (k7_relat_1(k2_zfmisc_1(A_19, B_20), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_235])).
% 2.23/1.37  tff(c_291, plain, (![A_70, B_71, C_72]: (r2_hidden(A_70, B_71) | ~r2_hidden(A_70, k1_relat_1(k7_relat_1(C_72, B_71))) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.23/1.37  tff(c_294, plain, (![A_70, A_19, B_20]: (r2_hidden(A_70, k1_xboole_0) | ~r2_hidden(A_70, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(superposition, [status(thm), theory('equality')], [c_244, c_291])).
% 2.23/1.37  tff(c_303, plain, (![A_70]: (r2_hidden(A_70, k1_xboole_0) | ~r2_hidden(A_70, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_294])).
% 2.23/1.37  tff(c_308, plain, (![A_73]: (~r2_hidden(A_73, k1_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_140, c_303])).
% 2.23/1.37  tff(c_313, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_308])).
% 2.23/1.37  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.23/1.37  tff(c_317, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_313, c_14])).
% 2.23/1.37  tff(c_28, plain, (![A_18]: (k2_xboole_0(k1_relat_1(A_18), k2_relat_1(A_18))=k3_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.23/1.37  tff(c_347, plain, (k2_xboole_0(k1_xboole_0, k2_relat_1(k1_xboole_0))=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_317, c_28])).
% 2.23/1.37  tff(c_355, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_61, c_160, c_34, c_347])).
% 2.23/1.37  tff(c_357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_355])).
% 2.23/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.37  
% 2.23/1.37  Inference rules
% 2.23/1.37  ----------------------
% 2.23/1.37  #Ref     : 0
% 2.23/1.37  #Sup     : 68
% 2.23/1.37  #Fact    : 0
% 2.23/1.37  #Define  : 0
% 2.23/1.37  #Split   : 0
% 2.23/1.37  #Chain   : 0
% 2.23/1.37  #Close   : 0
% 2.23/1.37  
% 2.23/1.37  Ordering : KBO
% 2.23/1.37  
% 2.23/1.37  Simplification rules
% 2.23/1.37  ----------------------
% 2.23/1.37  #Subsume      : 3
% 2.23/1.37  #Demod        : 32
% 2.23/1.37  #Tautology    : 47
% 2.23/1.37  #SimpNegUnit  : 3
% 2.23/1.37  #BackRed      : 3
% 2.23/1.37  
% 2.23/1.37  #Partial instantiations: 0
% 2.23/1.37  #Strategies tried      : 1
% 2.23/1.37  
% 2.23/1.37  Timing (in seconds)
% 2.23/1.37  ----------------------
% 2.23/1.38  Preprocessing        : 0.37
% 2.23/1.38  Parsing              : 0.18
% 2.23/1.38  CNF conversion       : 0.02
% 2.23/1.38  Main loop            : 0.18
% 2.23/1.38  Inferencing          : 0.07
% 2.23/1.38  Reduction            : 0.06
% 2.23/1.38  Demodulation         : 0.04
% 2.23/1.38  BG Simplification    : 0.02
% 2.23/1.38  Subsumption          : 0.03
% 2.23/1.38  Abstraction          : 0.01
% 2.23/1.38  MUC search           : 0.00
% 2.23/1.38  Cooper               : 0.00
% 2.23/1.38  Total                : 0.59
% 2.23/1.38  Index Insertion      : 0.00
% 2.23/1.38  Index Deletion       : 0.00
% 2.23/1.38  Index Matching       : 0.00
% 2.23/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
