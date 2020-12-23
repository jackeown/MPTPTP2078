%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:39 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   60 (  82 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   65 ( 107 expanded)
%              Number of equality atoms :   34 (  54 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_96,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_65,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_38,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    ! [A_21,B_22] :
      ( v1_relat_1(k7_relat_1(A_21,B_22))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_124,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_18,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_125,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    ! [A_36] : k3_xboole_0(A_36,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_125])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_135,plain,(
    ! [A_36] : k3_xboole_0(k1_xboole_0,A_36) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_2])).

tff(c_28,plain,(
    ! [B_18] : k2_zfmisc_1(k1_xboole_0,B_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_979,plain,(
    ! [B_92,A_93] :
      ( k3_xboole_0(k1_relat_1(B_92),A_93) = k1_relat_1(k7_relat_1(B_92,A_93))
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_50,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_206,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_50])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_210,plain,(
    k3_xboole_0(k1_relat_1('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_206,c_4])).

tff(c_1026,plain,
    ( k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_979,c_210])).

tff(c_1068,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1026])).

tff(c_34,plain,(
    ! [A_23] :
      ( k3_xboole_0(A_23,k2_zfmisc_1(k1_relat_1(A_23),k2_relat_1(A_23))) = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1079,plain,
    ( k3_xboole_0(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1('#skF_4','#skF_3')))) = k7_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1068,c_34])).

tff(c_1083,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_2,c_28,c_1079])).

tff(c_1084,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_1083])).

tff(c_1088,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1084])).

tff(c_1092,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1088])).

tff(c_1094,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1504,plain,(
    ! [B_135,A_136] :
      ( k3_xboole_0(k1_relat_1(B_135),A_136) = k1_relat_1(k7_relat_1(B_135,A_136))
      | ~ v1_relat_1(B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1724,plain,(
    ! [A_147,B_148] :
      ( k3_xboole_0(A_147,k1_relat_1(B_148)) = k1_relat_1(k7_relat_1(B_148,A_147))
      | ~ v1_relat_1(B_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1504,c_2])).

tff(c_1168,plain,(
    ! [A_98,B_99] :
      ( r1_xboole_0(A_98,B_99)
      | k3_xboole_0(A_98,B_99) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1093,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1174,plain,(
    k3_xboole_0(k1_relat_1('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1168,c_1093])).

tff(c_1181,plain,(
    k3_xboole_0('#skF_3',k1_relat_1('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1174])).

tff(c_1759,plain,
    ( k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1724,c_1181])).

tff(c_1798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_1094,c_1759])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.58  
% 3.22/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.58  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.22/1.58  
% 3.22/1.58  %Foreground sorts:
% 3.22/1.58  
% 3.22/1.58  
% 3.22/1.58  %Background operators:
% 3.22/1.58  
% 3.22/1.58  
% 3.22/1.58  %Foreground operators:
% 3.22/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.22/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.22/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.22/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.22/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.22/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.22/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.22/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.22/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.22/1.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.22/1.58  
% 3.22/1.59  tff(f_107, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 3.22/1.59  tff(f_96, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.22/1.59  tff(f_89, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.22/1.59  tff(f_65, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.22/1.59  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.22/1.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.22/1.59  tff(f_83, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.22/1.59  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 3.22/1.59  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.22/1.59  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.22/1.59  tff(c_38, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.22/1.59  tff(c_32, plain, (![A_21, B_22]: (v1_relat_1(k7_relat_1(A_21, B_22)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.22/1.59  tff(c_44, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.22/1.59  tff(c_124, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_44])).
% 3.22/1.59  tff(c_18, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.22/1.59  tff(c_125, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.59  tff(c_130, plain, (![A_36]: (k3_xboole_0(A_36, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_125])).
% 3.22/1.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.22/1.59  tff(c_135, plain, (![A_36]: (k3_xboole_0(k1_xboole_0, A_36)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_130, c_2])).
% 3.22/1.59  tff(c_28, plain, (![B_18]: (k2_zfmisc_1(k1_xboole_0, B_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.22/1.59  tff(c_979, plain, (![B_92, A_93]: (k3_xboole_0(k1_relat_1(B_92), A_93)=k1_relat_1(k7_relat_1(B_92, A_93)) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.22/1.59  tff(c_50, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.22/1.59  tff(c_206, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_124, c_50])).
% 3.22/1.59  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.59  tff(c_210, plain, (k3_xboole_0(k1_relat_1('#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_206, c_4])).
% 3.22/1.59  tff(c_1026, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_979, c_210])).
% 3.22/1.59  tff(c_1068, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1026])).
% 3.22/1.59  tff(c_34, plain, (![A_23]: (k3_xboole_0(A_23, k2_zfmisc_1(k1_relat_1(A_23), k2_relat_1(A_23)))=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.22/1.59  tff(c_1079, plain, (k3_xboole_0(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k7_relat_1('#skF_4', '#skF_3'))))=k7_relat_1('#skF_4', '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1068, c_34])).
% 3.22/1.59  tff(c_1083, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_2, c_28, c_1079])).
% 3.22/1.59  tff(c_1084, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_124, c_1083])).
% 3.22/1.59  tff(c_1088, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_1084])).
% 3.22/1.59  tff(c_1092, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1088])).
% 3.22/1.59  tff(c_1094, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_44])).
% 3.22/1.59  tff(c_1504, plain, (![B_135, A_136]: (k3_xboole_0(k1_relat_1(B_135), A_136)=k1_relat_1(k7_relat_1(B_135, A_136)) | ~v1_relat_1(B_135))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.22/1.59  tff(c_1724, plain, (![A_147, B_148]: (k3_xboole_0(A_147, k1_relat_1(B_148))=k1_relat_1(k7_relat_1(B_148, A_147)) | ~v1_relat_1(B_148))), inference(superposition, [status(thm), theory('equality')], [c_1504, c_2])).
% 3.22/1.59  tff(c_1168, plain, (![A_98, B_99]: (r1_xboole_0(A_98, B_99) | k3_xboole_0(A_98, B_99)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.59  tff(c_1093, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.22/1.59  tff(c_1174, plain, (k3_xboole_0(k1_relat_1('#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1168, c_1093])).
% 3.22/1.59  tff(c_1181, plain, (k3_xboole_0('#skF_3', k1_relat_1('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1174])).
% 3.22/1.59  tff(c_1759, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1724, c_1181])).
% 3.22/1.59  tff(c_1798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_1094, c_1759])).
% 3.22/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.59  
% 3.22/1.59  Inference rules
% 3.22/1.59  ----------------------
% 3.22/1.59  #Ref     : 0
% 3.22/1.59  #Sup     : 425
% 3.22/1.59  #Fact    : 0
% 3.22/1.59  #Define  : 0
% 3.22/1.59  #Split   : 1
% 3.22/1.59  #Chain   : 0
% 3.22/1.59  #Close   : 0
% 3.22/1.59  
% 3.22/1.59  Ordering : KBO
% 3.22/1.59  
% 3.22/1.59  Simplification rules
% 3.22/1.59  ----------------------
% 3.22/1.59  #Subsume      : 82
% 3.22/1.59  #Demod        : 180
% 3.22/1.59  #Tautology    : 195
% 3.22/1.59  #SimpNegUnit  : 11
% 3.22/1.59  #BackRed      : 1
% 3.22/1.59  
% 3.22/1.59  #Partial instantiations: 0
% 3.22/1.59  #Strategies tried      : 1
% 3.22/1.59  
% 3.22/1.59  Timing (in seconds)
% 3.22/1.59  ----------------------
% 3.22/1.59  Preprocessing        : 0.33
% 3.22/1.59  Parsing              : 0.18
% 3.22/1.59  CNF conversion       : 0.02
% 3.22/1.59  Main loop            : 0.44
% 3.22/1.59  Inferencing          : 0.16
% 3.22/1.59  Reduction            : 0.15
% 3.22/1.59  Demodulation         : 0.11
% 3.22/1.59  BG Simplification    : 0.02
% 3.22/1.60  Subsumption          : 0.08
% 3.22/1.60  Abstraction          : 0.02
% 3.22/1.60  MUC search           : 0.00
% 3.22/1.60  Cooper               : 0.00
% 3.22/1.60  Total                : 0.79
% 3.22/1.60  Index Insertion      : 0.00
% 3.22/1.60  Index Deletion       : 0.00
% 3.22/1.60  Index Matching       : 0.00
% 3.22/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
