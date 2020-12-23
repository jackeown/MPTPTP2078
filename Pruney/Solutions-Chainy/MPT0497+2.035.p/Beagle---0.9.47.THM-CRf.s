%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:44 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   60 (  73 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 107 expanded)
%              Number of equality atoms :   27 (  38 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_56,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_xboole_0(k2_relat_1(A),k1_relat_1(B))
           => k5_relat_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_36,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_99,plain,(
    k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_42,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_123,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_42])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_126,plain,(
    r1_xboole_0('#skF_2',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_18,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [A_18] : k2_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_181,plain,(
    ! [A_48,B_49] :
      ( k5_relat_1(A_48,B_49) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_48),k1_relat_1(B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_190,plain,(
    ! [A_18,B_49] :
      ( k5_relat_1(k6_relat_1(A_18),B_49) = k1_xboole_0
      | ~ r1_xboole_0(A_18,k1_relat_1(B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_181])).

tff(c_317,plain,(
    ! [A_61,B_62] :
      ( k5_relat_1(k6_relat_1(A_61),B_62) = k1_xboole_0
      | ~ r1_xboole_0(A_61,k1_relat_1(B_62))
      | ~ v1_relat_1(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_190])).

tff(c_326,plain,
    ( k5_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_126,c_317])).

tff(c_335,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_326])).

tff(c_32,plain,(
    ! [A_21,B_22] :
      ( k5_relat_1(k6_relat_1(A_21),B_22) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_341,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_32])).

tff(c_348,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_341])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_348])).

tff(c_351,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_10,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_92,plain,(
    ! [A_28,B_29] : ~ r2_hidden(A_28,k2_zfmisc_1(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_98,plain,(
    ! [A_8] : ~ r2_hidden(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_92])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_352,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_403,plain,(
    ! [B_77,A_78] :
      ( k3_xboole_0(k1_relat_1(B_77),A_78) = k1_relat_1(k7_relat_1(B_77,A_78))
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_530,plain,(
    ! [B_96,A_97] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_96),A_97),k1_relat_1(k7_relat_1(B_96,A_97)))
      | r1_xboole_0(k1_relat_1(B_96),A_97)
      | ~ v1_relat_1(B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_4])).

tff(c_545,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_3'),'#skF_2'),k1_relat_1(k1_xboole_0))
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_530])).

tff(c_560,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_3'),'#skF_2'),k1_xboole_0)
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_22,c_545])).

tff(c_562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_351,c_98,c_560])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:36:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.33  
% 2.26/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.34  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.57/1.34  
% 2.57/1.34  %Foreground sorts:
% 2.57/1.34  
% 2.57/1.34  
% 2.57/1.34  %Background operators:
% 2.57/1.34  
% 2.57/1.34  
% 2.57/1.34  %Foreground operators:
% 2.57/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.57/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.57/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.57/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.57/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.57/1.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.57/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.57/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.57/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.57/1.34  
% 2.57/1.35  tff(f_87, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.57/1.35  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.57/1.35  tff(f_56, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.57/1.35  tff(f_72, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.57/1.35  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k1_relat_1(B)) => (k5_relat_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_relat_1)).
% 2.57/1.35  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.57/1.35  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.57/1.35  tff(f_52, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.57/1.35  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.57/1.35  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.57/1.35  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.57/1.35  tff(c_36, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.57/1.35  tff(c_99, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.57/1.35  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.57/1.35  tff(c_42, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.57/1.35  tff(c_123, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_99, c_42])).
% 2.57/1.35  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.57/1.35  tff(c_126, plain, (r1_xboole_0('#skF_2', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_123, c_2])).
% 2.57/1.35  tff(c_18, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.57/1.35  tff(c_28, plain, (![A_18]: (k2_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.57/1.35  tff(c_181, plain, (![A_48, B_49]: (k5_relat_1(A_48, B_49)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_48), k1_relat_1(B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.57/1.35  tff(c_190, plain, (![A_18, B_49]: (k5_relat_1(k6_relat_1(A_18), B_49)=k1_xboole_0 | ~r1_xboole_0(A_18, k1_relat_1(B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_181])).
% 2.57/1.35  tff(c_317, plain, (![A_61, B_62]: (k5_relat_1(k6_relat_1(A_61), B_62)=k1_xboole_0 | ~r1_xboole_0(A_61, k1_relat_1(B_62)) | ~v1_relat_1(B_62))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_190])).
% 2.57/1.35  tff(c_326, plain, (k5_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_126, c_317])).
% 2.57/1.35  tff(c_335, plain, (k5_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_326])).
% 2.57/1.35  tff(c_32, plain, (![A_21, B_22]: (k5_relat_1(k6_relat_1(A_21), B_22)=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.57/1.35  tff(c_341, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_335, c_32])).
% 2.57/1.35  tff(c_348, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_341])).
% 2.57/1.35  tff(c_350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_348])).
% 2.57/1.35  tff(c_351, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 2.57/1.35  tff(c_10, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.57/1.35  tff(c_92, plain, (![A_28, B_29]: (~r2_hidden(A_28, k2_zfmisc_1(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.57/1.35  tff(c_98, plain, (![A_8]: (~r2_hidden(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_92])).
% 2.57/1.35  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.57/1.35  tff(c_352, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.57/1.35  tff(c_403, plain, (![B_77, A_78]: (k3_xboole_0(k1_relat_1(B_77), A_78)=k1_relat_1(k7_relat_1(B_77, A_78)) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.57/1.35  tff(c_4, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.57/1.35  tff(c_530, plain, (![B_96, A_97]: (r2_hidden('#skF_1'(k1_relat_1(B_96), A_97), k1_relat_1(k7_relat_1(B_96, A_97))) | r1_xboole_0(k1_relat_1(B_96), A_97) | ~v1_relat_1(B_96))), inference(superposition, [status(thm), theory('equality')], [c_403, c_4])).
% 2.57/1.35  tff(c_545, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_3'), '#skF_2'), k1_relat_1(k1_xboole_0)) | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_352, c_530])).
% 2.57/1.35  tff(c_560, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_3'), '#skF_2'), k1_xboole_0) | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_22, c_545])).
% 2.57/1.35  tff(c_562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_351, c_98, c_560])).
% 2.57/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.35  
% 2.57/1.35  Inference rules
% 2.57/1.35  ----------------------
% 2.57/1.35  #Ref     : 0
% 2.57/1.35  #Sup     : 123
% 2.57/1.35  #Fact    : 0
% 2.57/1.35  #Define  : 0
% 2.57/1.35  #Split   : 4
% 2.57/1.35  #Chain   : 0
% 2.57/1.35  #Close   : 0
% 2.57/1.35  
% 2.57/1.35  Ordering : KBO
% 2.57/1.35  
% 2.57/1.35  Simplification rules
% 2.57/1.35  ----------------------
% 2.57/1.35  #Subsume      : 24
% 2.57/1.35  #Demod        : 51
% 2.57/1.35  #Tautology    : 63
% 2.57/1.35  #SimpNegUnit  : 7
% 2.57/1.35  #BackRed      : 0
% 2.57/1.35  
% 2.57/1.35  #Partial instantiations: 0
% 2.57/1.35  #Strategies tried      : 1
% 2.57/1.35  
% 2.57/1.35  Timing (in seconds)
% 2.57/1.35  ----------------------
% 2.57/1.35  Preprocessing        : 0.30
% 2.57/1.35  Parsing              : 0.16
% 2.57/1.35  CNF conversion       : 0.02
% 2.57/1.35  Main loop            : 0.27
% 2.57/1.35  Inferencing          : 0.10
% 2.57/1.35  Reduction            : 0.09
% 2.57/1.35  Demodulation         : 0.06
% 2.57/1.35  BG Simplification    : 0.01
% 2.57/1.35  Subsumption          : 0.04
% 2.57/1.35  Abstraction          : 0.02
% 2.57/1.35  MUC search           : 0.00
% 2.57/1.35  Cooper               : 0.00
% 2.57/1.35  Total                : 0.60
% 2.57/1.35  Index Insertion      : 0.00
% 2.57/1.35  Index Deletion       : 0.00
% 2.57/1.35  Index Matching       : 0.00
% 2.57/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
