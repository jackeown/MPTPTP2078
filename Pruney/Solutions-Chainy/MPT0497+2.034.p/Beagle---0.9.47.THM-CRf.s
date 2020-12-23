%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:43 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   63 (  76 expanded)
%              Number of leaves         :   31 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   83 ( 113 expanded)
%              Number of equality atoms :   27 (  38 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_66,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_xboole_0(k2_relat_1(A),k1_relat_1(B))
           => k5_relat_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(c_40,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_103,plain,(
    k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_46,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_141,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_46])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_144,plain,(
    r1_xboole_0('#skF_2',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_141,c_2])).

tff(c_22,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_255,plain,(
    ! [A_61,B_62] :
      ( k5_relat_1(A_61,B_62) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_61),k1_relat_1(B_62))
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_264,plain,(
    ! [A_20,B_62] :
      ( k5_relat_1(k6_relat_1(A_20),B_62) = k1_xboole_0
      | ~ r1_xboole_0(A_20,k1_relat_1(B_62))
      | ~ v1_relat_1(B_62)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_255])).

tff(c_482,plain,(
    ! [A_78,B_79] :
      ( k5_relat_1(k6_relat_1(A_78),B_79) = k1_xboole_0
      | ~ r1_xboole_0(A_78,k1_relat_1(B_79))
      | ~ v1_relat_1(B_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_264])).

tff(c_491,plain,
    ( k5_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_144,c_482])).

tff(c_504,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_491])).

tff(c_36,plain,(
    ! [A_23,B_24] :
      ( k5_relat_1(k6_relat_1(A_23),B_24) = k7_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_513,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_36])).

tff(c_520,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_513])).

tff(c_522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_520])).

tff(c_523,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_560,plain,(
    ! [A_87,B_88] :
      ( r2_hidden('#skF_1'(A_87,B_88),A_87)
      | r1_xboole_0(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_96,plain,(
    ! [A_30,B_31] : ~ r2_hidden(A_30,k2_zfmisc_1(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_102,plain,(
    ! [A_10] : ~ r2_hidden(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_96])).

tff(c_565,plain,(
    ! [B_88] : r1_xboole_0(k1_xboole_0,B_88) ),
    inference(resolution,[status(thm)],[c_560,c_102])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_524,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_605,plain,(
    ! [B_100,A_101] :
      ( k3_xboole_0(k1_relat_1(B_100),A_101) = k1_relat_1(k7_relat_1(B_100,A_101))
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( ~ r1_xboole_0(k3_xboole_0(A_8,B_9),B_9)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_834,plain,(
    ! [B_117,A_118] :
      ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(B_117,A_118)),A_118)
      | r1_xboole_0(k1_relat_1(B_117),A_118)
      | ~ v1_relat_1(B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_10])).

tff(c_853,plain,
    ( ~ r1_xboole_0(k1_relat_1(k1_xboole_0),'#skF_2')
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_834])).

tff(c_865,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_565,c_26,c_853])).

tff(c_867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_523,c_865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.44  
% 2.53/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.44  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.53/1.44  
% 2.53/1.44  %Foreground sorts:
% 2.53/1.44  
% 2.53/1.44  
% 2.53/1.44  %Background operators:
% 2.53/1.44  
% 2.53/1.44  
% 2.53/1.44  %Foreground operators:
% 2.53/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.53/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.53/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.53/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.53/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.53/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.53/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.53/1.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.53/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.53/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.53/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.53/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.53/1.44  
% 2.53/1.45  tff(f_97, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.53/1.45  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.53/1.45  tff(f_66, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.53/1.45  tff(f_82, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.53/1.45  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k1_relat_1(B)) => (k5_relat_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_relat_1)).
% 2.53/1.45  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.53/1.45  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.53/1.45  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.53/1.45  tff(f_62, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.53/1.45  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.53/1.45  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.53/1.45  tff(f_53, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 2.53/1.45  tff(c_40, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.53/1.45  tff(c_103, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 2.53/1.45  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.53/1.45  tff(c_46, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.53/1.45  tff(c_141, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_103, c_46])).
% 2.53/1.45  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.53/1.45  tff(c_144, plain, (r1_xboole_0('#skF_2', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_141, c_2])).
% 2.53/1.45  tff(c_22, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.53/1.45  tff(c_32, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.53/1.45  tff(c_255, plain, (![A_61, B_62]: (k5_relat_1(A_61, B_62)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_61), k1_relat_1(B_62)) | ~v1_relat_1(B_62) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.53/1.45  tff(c_264, plain, (![A_20, B_62]: (k5_relat_1(k6_relat_1(A_20), B_62)=k1_xboole_0 | ~r1_xboole_0(A_20, k1_relat_1(B_62)) | ~v1_relat_1(B_62) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_255])).
% 2.53/1.45  tff(c_482, plain, (![A_78, B_79]: (k5_relat_1(k6_relat_1(A_78), B_79)=k1_xboole_0 | ~r1_xboole_0(A_78, k1_relat_1(B_79)) | ~v1_relat_1(B_79))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_264])).
% 2.53/1.45  tff(c_491, plain, (k5_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_144, c_482])).
% 2.53/1.45  tff(c_504, plain, (k5_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_491])).
% 2.53/1.45  tff(c_36, plain, (![A_23, B_24]: (k5_relat_1(k6_relat_1(A_23), B_24)=k7_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.53/1.45  tff(c_513, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_504, c_36])).
% 2.53/1.45  tff(c_520, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_513])).
% 2.53/1.45  tff(c_522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_520])).
% 2.53/1.45  tff(c_523, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 2.53/1.45  tff(c_560, plain, (![A_87, B_88]: (r2_hidden('#skF_1'(A_87, B_88), A_87) | r1_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.53/1.45  tff(c_14, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.53/1.45  tff(c_96, plain, (![A_30, B_31]: (~r2_hidden(A_30, k2_zfmisc_1(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.53/1.45  tff(c_102, plain, (![A_10]: (~r2_hidden(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_96])).
% 2.53/1.45  tff(c_565, plain, (![B_88]: (r1_xboole_0(k1_xboole_0, B_88))), inference(resolution, [status(thm)], [c_560, c_102])).
% 2.53/1.45  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.53/1.45  tff(c_524, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 2.53/1.45  tff(c_605, plain, (![B_100, A_101]: (k3_xboole_0(k1_relat_1(B_100), A_101)=k1_relat_1(k7_relat_1(B_100, A_101)) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.53/1.45  tff(c_10, plain, (![A_8, B_9]: (~r1_xboole_0(k3_xboole_0(A_8, B_9), B_9) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.53/1.45  tff(c_834, plain, (![B_117, A_118]: (~r1_xboole_0(k1_relat_1(k7_relat_1(B_117, A_118)), A_118) | r1_xboole_0(k1_relat_1(B_117), A_118) | ~v1_relat_1(B_117))), inference(superposition, [status(thm), theory('equality')], [c_605, c_10])).
% 2.53/1.45  tff(c_853, plain, (~r1_xboole_0(k1_relat_1(k1_xboole_0), '#skF_2') | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_524, c_834])).
% 2.53/1.45  tff(c_865, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_565, c_26, c_853])).
% 2.53/1.45  tff(c_867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_523, c_865])).
% 2.53/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.45  
% 2.53/1.45  Inference rules
% 2.53/1.45  ----------------------
% 2.53/1.45  #Ref     : 0
% 2.53/1.45  #Sup     : 181
% 2.53/1.45  #Fact    : 0
% 2.53/1.45  #Define  : 0
% 2.53/1.45  #Split   : 4
% 2.53/1.45  #Chain   : 0
% 2.53/1.45  #Close   : 0
% 2.53/1.45  
% 2.53/1.45  Ordering : KBO
% 2.53/1.45  
% 2.53/1.45  Simplification rules
% 2.53/1.45  ----------------------
% 2.53/1.45  #Subsume      : 22
% 2.53/1.45  #Demod        : 103
% 2.53/1.45  #Tautology    : 104
% 2.53/1.45  #SimpNegUnit  : 4
% 2.53/1.45  #BackRed      : 0
% 2.53/1.45  
% 2.53/1.45  #Partial instantiations: 0
% 2.53/1.45  #Strategies tried      : 1
% 2.53/1.45  
% 2.53/1.45  Timing (in seconds)
% 2.53/1.45  ----------------------
% 2.84/1.46  Preprocessing        : 0.33
% 2.84/1.46  Parsing              : 0.18
% 2.84/1.46  CNF conversion       : 0.02
% 2.84/1.46  Main loop            : 0.30
% 2.84/1.46  Inferencing          : 0.12
% 2.84/1.46  Reduction            : 0.09
% 2.84/1.46  Demodulation         : 0.06
% 2.84/1.46  BG Simplification    : 0.02
% 2.84/1.46  Subsumption          : 0.05
% 2.84/1.46  Abstraction          : 0.02
% 2.84/1.46  MUC search           : 0.00
% 2.84/1.46  Cooper               : 0.00
% 2.84/1.46  Total                : 0.66
% 2.84/1.46  Index Insertion      : 0.00
% 2.84/1.46  Index Deletion       : 0.00
% 2.84/1.46  Index Matching       : 0.00
% 2.84/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
