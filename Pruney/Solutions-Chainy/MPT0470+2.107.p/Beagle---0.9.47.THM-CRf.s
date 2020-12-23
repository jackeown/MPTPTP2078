%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:15 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 111 expanded)
%              Number of leaves         :   31 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  125 ( 190 expanded)
%              Number of equality atoms :   33 (  63 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_98,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_42,plain,
    ( k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_84,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_93,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_1'(A_45),A_45)
      | v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_85,plain,(
    ! [A_42,B_43] : ~ r2_hidden(A_42,k2_zfmisc_1(A_42,B_43)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_91,plain,(
    ! [A_5] : ~ r2_hidden(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_85])).

tff(c_98,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_93,c_91])).

tff(c_28,plain,(
    ! [A_27,B_28] :
      ( v1_relat_1(k5_relat_1(A_27,B_28))
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_207,plain,(
    ! [A_67,B_68] :
      ( k1_relat_1(k5_relat_1(A_67,B_68)) = k1_relat_1(A_67)
      | ~ r1_tarski(k2_relat_1(A_67),k1_relat_1(B_68))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_216,plain,(
    ! [B_68] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_68)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_68))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_207])).

tff(c_223,plain,(
    ! [B_69] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_69)) = k1_xboole_0
      | ~ v1_relat_1(B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_12,c_40,c_216])).

tff(c_30,plain,(
    ! [A_29] :
      ( ~ v1_xboole_0(k1_relat_1(A_29))
      | ~ v1_relat_1(A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_232,plain,(
    ! [B_69] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_69))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_69))
      | ~ v1_relat_1(B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_30])).

tff(c_245,plain,(
    ! [B_72] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_72))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_72))
      | ~ v1_relat_1(B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_232])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_255,plain,(
    ! [B_74] :
      ( k5_relat_1(k1_xboole_0,B_74) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_74))
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_245,c_4])).

tff(c_259,plain,(
    ! [B_28] :
      ( k5_relat_1(k1_xboole_0,B_28) = k1_xboole_0
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_255])).

tff(c_279,plain,(
    ! [B_77] :
      ( k5_relat_1(k1_xboole_0,B_77) = k1_xboole_0
      | ~ v1_relat_1(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_259])).

tff(c_288,plain,(
    k5_relat_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_279])).

tff(c_294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_288])).

tff(c_295,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_309,plain,(
    ! [A_81] :
      ( r2_hidden('#skF_1'(A_81),A_81)
      | v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_301,plain,(
    ! [A_78,B_79] : ~ r2_hidden(A_78,k2_zfmisc_1(A_78,B_79)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_307,plain,(
    ! [A_5] : ~ r2_hidden(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_301])).

tff(c_314,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_309,c_307])).

tff(c_368,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_94,B_95)),k2_relat_1(B_95))
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_376,plain,(
    ! [A_94] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_94,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_368])).

tff(c_382,plain,(
    ! [A_96] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_96,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_376])).

tff(c_328,plain,(
    ! [B_87,A_88] :
      ( B_87 = A_88
      | ~ r1_tarski(B_87,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_337,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_328])).

tff(c_392,plain,(
    ! [A_97] :
      ( k2_relat_1(k5_relat_1(A_97,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_382,c_337])).

tff(c_32,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(k2_relat_1(A_30))
      | ~ v1_relat_1(A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_407,plain,(
    ! [A_97] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_97,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_97,k1_xboole_0))
      | ~ v1_relat_1(A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_32])).

tff(c_438,plain,(
    ! [A_105] :
      ( ~ v1_relat_1(k5_relat_1(A_105,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_105,k1_xboole_0))
      | ~ v1_relat_1(A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_407])).

tff(c_583,plain,(
    ! [A_114] :
      ( k5_relat_1(A_114,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_114,k1_xboole_0))
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_438,c_4])).

tff(c_590,plain,(
    ! [A_27] :
      ( k5_relat_1(A_27,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_27) ) ),
    inference(resolution,[status(thm)],[c_28,c_583])).

tff(c_596,plain,(
    ! [A_115] :
      ( k5_relat_1(A_115,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_590])).

tff(c_605,plain,(
    k5_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_596])).

tff(c_612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_605])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:36:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.32  
% 2.11/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.32  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.11/1.32  
% 2.11/1.32  %Foreground sorts:
% 2.11/1.32  
% 2.11/1.32  
% 2.11/1.32  %Background operators:
% 2.11/1.32  
% 2.11/1.32  
% 2.11/1.32  %Foreground operators:
% 2.11/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.11/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.11/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.11/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.11/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.11/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.11/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.11/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.11/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.11/1.32  
% 2.55/1.34  tff(f_105, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.55/1.34  tff(f_57, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.55/1.34  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.55/1.34  tff(f_47, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.55/1.34  tff(f_63, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.55/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.55/1.34  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.55/1.34  tff(f_98, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.55/1.34  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.55/1.34  tff(f_71, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.55/1.34  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.55/1.34  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.55/1.34  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.55/1.34  tff(f_79, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.55/1.34  tff(c_42, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.55/1.34  tff(c_84, plain, (k5_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 2.55/1.34  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.55/1.34  tff(c_93, plain, (![A_45]: (r2_hidden('#skF_1'(A_45), A_45) | v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.55/1.34  tff(c_16, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.55/1.34  tff(c_85, plain, (![A_42, B_43]: (~r2_hidden(A_42, k2_zfmisc_1(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.55/1.34  tff(c_91, plain, (![A_5]: (~r2_hidden(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_85])).
% 2.55/1.34  tff(c_98, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_93, c_91])).
% 2.55/1.34  tff(c_28, plain, (![A_27, B_28]: (v1_relat_1(k5_relat_1(A_27, B_28)) | ~v1_relat_1(B_28) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.55/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.55/1.34  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.55/1.34  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.55/1.34  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.55/1.34  tff(c_207, plain, (![A_67, B_68]: (k1_relat_1(k5_relat_1(A_67, B_68))=k1_relat_1(A_67) | ~r1_tarski(k2_relat_1(A_67), k1_relat_1(B_68)) | ~v1_relat_1(B_68) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.55/1.34  tff(c_216, plain, (![B_68]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_68))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_68)) | ~v1_relat_1(B_68) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_207])).
% 2.55/1.34  tff(c_223, plain, (![B_69]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_69))=k1_xboole_0 | ~v1_relat_1(B_69))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_12, c_40, c_216])).
% 2.55/1.34  tff(c_30, plain, (![A_29]: (~v1_xboole_0(k1_relat_1(A_29)) | ~v1_relat_1(A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.55/1.34  tff(c_232, plain, (![B_69]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_69)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_69)) | ~v1_relat_1(B_69))), inference(superposition, [status(thm), theory('equality')], [c_223, c_30])).
% 2.55/1.34  tff(c_245, plain, (![B_72]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_72)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_72)) | ~v1_relat_1(B_72))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_232])).
% 2.55/1.34  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.55/1.34  tff(c_255, plain, (![B_74]: (k5_relat_1(k1_xboole_0, B_74)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_74)) | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_245, c_4])).
% 2.55/1.34  tff(c_259, plain, (![B_28]: (k5_relat_1(k1_xboole_0, B_28)=k1_xboole_0 | ~v1_relat_1(B_28) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_255])).
% 2.55/1.34  tff(c_279, plain, (![B_77]: (k5_relat_1(k1_xboole_0, B_77)=k1_xboole_0 | ~v1_relat_1(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_259])).
% 2.55/1.34  tff(c_288, plain, (k5_relat_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_279])).
% 2.55/1.34  tff(c_294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_288])).
% 2.55/1.34  tff(c_295, plain, (k5_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.55/1.34  tff(c_309, plain, (![A_81]: (r2_hidden('#skF_1'(A_81), A_81) | v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.55/1.34  tff(c_301, plain, (![A_78, B_79]: (~r2_hidden(A_78, k2_zfmisc_1(A_78, B_79)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.55/1.34  tff(c_307, plain, (![A_5]: (~r2_hidden(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_301])).
% 2.55/1.34  tff(c_314, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_309, c_307])).
% 2.55/1.34  tff(c_368, plain, (![A_94, B_95]: (r1_tarski(k2_relat_1(k5_relat_1(A_94, B_95)), k2_relat_1(B_95)) | ~v1_relat_1(B_95) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.55/1.34  tff(c_376, plain, (![A_94]: (r1_tarski(k2_relat_1(k5_relat_1(A_94, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_94))), inference(superposition, [status(thm), theory('equality')], [c_38, c_368])).
% 2.55/1.34  tff(c_382, plain, (![A_96]: (r1_tarski(k2_relat_1(k5_relat_1(A_96, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_376])).
% 2.55/1.34  tff(c_328, plain, (![B_87, A_88]: (B_87=A_88 | ~r1_tarski(B_87, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.55/1.34  tff(c_337, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_328])).
% 2.55/1.34  tff(c_392, plain, (![A_97]: (k2_relat_1(k5_relat_1(A_97, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_382, c_337])).
% 2.55/1.34  tff(c_32, plain, (![A_30]: (~v1_xboole_0(k2_relat_1(A_30)) | ~v1_relat_1(A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.55/1.34  tff(c_407, plain, (![A_97]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_97, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_97, k1_xboole_0)) | ~v1_relat_1(A_97))), inference(superposition, [status(thm), theory('equality')], [c_392, c_32])).
% 2.55/1.34  tff(c_438, plain, (![A_105]: (~v1_relat_1(k5_relat_1(A_105, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_105, k1_xboole_0)) | ~v1_relat_1(A_105))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_407])).
% 2.55/1.34  tff(c_583, plain, (![A_114]: (k5_relat_1(A_114, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_114, k1_xboole_0)) | ~v1_relat_1(A_114))), inference(resolution, [status(thm)], [c_438, c_4])).
% 2.55/1.34  tff(c_590, plain, (![A_27]: (k5_relat_1(A_27, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_27))), inference(resolution, [status(thm)], [c_28, c_583])).
% 2.55/1.34  tff(c_596, plain, (![A_115]: (k5_relat_1(A_115, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_590])).
% 2.55/1.34  tff(c_605, plain, (k5_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_596])).
% 2.55/1.34  tff(c_612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_295, c_605])).
% 2.55/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.34  
% 2.55/1.34  Inference rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Ref     : 2
% 2.55/1.34  #Sup     : 116
% 2.55/1.34  #Fact    : 0
% 2.55/1.34  #Define  : 0
% 2.55/1.34  #Split   : 1
% 2.55/1.34  #Chain   : 0
% 2.55/1.34  #Close   : 0
% 2.55/1.34  
% 2.55/1.34  Ordering : KBO
% 2.55/1.34  
% 2.55/1.34  Simplification rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Subsume      : 12
% 2.55/1.34  #Demod        : 115
% 2.55/1.34  #Tautology    : 64
% 2.55/1.34  #SimpNegUnit  : 2
% 2.55/1.34  #BackRed      : 0
% 2.55/1.34  
% 2.55/1.34  #Partial instantiations: 0
% 2.55/1.34  #Strategies tried      : 1
% 2.55/1.34  
% 2.55/1.34  Timing (in seconds)
% 2.55/1.34  ----------------------
% 2.55/1.34  Preprocessing        : 0.29
% 2.55/1.34  Parsing              : 0.16
% 2.55/1.34  CNF conversion       : 0.02
% 2.55/1.34  Main loop            : 0.27
% 2.55/1.34  Inferencing          : 0.11
% 2.55/1.34  Reduction            : 0.08
% 2.55/1.34  Demodulation         : 0.05
% 2.55/1.34  BG Simplification    : 0.01
% 2.55/1.34  Subsumption          : 0.05
% 2.55/1.34  Abstraction          : 0.01
% 2.55/1.34  MUC search           : 0.00
% 2.55/1.34  Cooper               : 0.00
% 2.55/1.34  Total                : 0.60
% 2.55/1.34  Index Insertion      : 0.00
% 2.55/1.34  Index Deletion       : 0.00
% 2.55/1.34  Index Matching       : 0.00
% 2.55/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
