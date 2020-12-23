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
% DateTime   : Thu Dec  3 10:02:37 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   58 (  66 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 111 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

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

tff(f_69,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_57,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k3_xboole_0(A_17,B_18))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_69,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(A_30,B_31)
      | k3_xboole_0(A_30,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_78,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_36])).

tff(c_18,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_133,plain,(
    ! [A_42,B_43,C_44] :
      ( ~ r1_xboole_0(A_42,B_43)
      | ~ r2_hidden(C_44,B_43)
      | ~ r2_hidden(C_44,A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_143,plain,(
    ! [C_45] : ~ r2_hidden(C_45,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_133])).

tff(c_153,plain,(
    ! [B_4] : r1_xboole_0(k1_xboole_0,B_4) ),
    inference(resolution,[status(thm)],[c_10,c_143])).

tff(c_299,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( ~ r1_xboole_0(A_62,B_63)
      | r1_xboole_0(k2_zfmisc_1(A_62,C_64),k2_zfmisc_1(B_63,D_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [A_12] :
      ( ~ r1_xboole_0(A_12,A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_354,plain,(
    ! [B_67,D_68] :
      ( k2_zfmisc_1(B_67,D_68) = k1_xboole_0
      | ~ r1_xboole_0(B_67,B_67) ) ),
    inference(resolution,[status(thm)],[c_299,c_24])).

tff(c_371,plain,(
    ! [D_68] : k2_zfmisc_1(k1_xboole_0,D_68) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_153,c_354])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_79,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),k1_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_79])).

tff(c_503,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_85,B_86)),k3_xboole_0(k1_relat_1(A_85),k1_relat_1(B_86)))
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_517,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0('#skF_2','#skF_3')),k1_xboole_0)
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_503])).

tff(c_525,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0('#skF_2','#skF_3')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_517])).

tff(c_20,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_109,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(B_37,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_118,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_109])).

tff(c_533,plain,(
    k1_relat_1(k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_525,c_118])).

tff(c_34,plain,(
    ! [A_22] :
      ( k3_xboole_0(A_22,k2_zfmisc_1(k1_relat_1(A_22),k2_relat_1(A_22))) = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_551,plain,
    ( k3_xboole_0(k3_xboole_0('#skF_2','#skF_3'),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k3_xboole_0('#skF_2','#skF_3')))) = k3_xboole_0('#skF_2','#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_34])).

tff(c_558,plain,
    ( k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_371,c_551])).

tff(c_559,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_558])).

tff(c_563,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_559])).

tff(c_567,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_563])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.33  
% 2.19/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.19/1.33  
% 2.19/1.33  %Foreground sorts:
% 2.19/1.33  
% 2.19/1.33  
% 2.19/1.33  %Background operators:
% 2.19/1.33  
% 2.19/1.33  
% 2.19/1.33  %Foreground operators:
% 2.19/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.19/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.33  
% 2.60/1.34  tff(f_100, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t214_relat_1)).
% 2.60/1.34  tff(f_79, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.60/1.34  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.60/1.34  tff(f_55, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.60/1.34  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.60/1.34  tff(f_69, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.60/1.34  tff(f_75, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.60/1.34  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relat_1)).
% 2.60/1.34  tff(f_57, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.60/1.34  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.60/1.34  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 2.60/1.34  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.60/1.34  tff(c_30, plain, (![A_17, B_18]: (v1_relat_1(k3_xboole_0(A_17, B_18)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.60/1.34  tff(c_69, plain, (![A_30, B_31]: (r1_xboole_0(A_30, B_31) | k3_xboole_0(A_30, B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.34  tff(c_36, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.60/1.34  tff(c_78, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_69, c_36])).
% 2.60/1.34  tff(c_18, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.60/1.34  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.60/1.34  tff(c_22, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.60/1.34  tff(c_133, plain, (![A_42, B_43, C_44]: (~r1_xboole_0(A_42, B_43) | ~r2_hidden(C_44, B_43) | ~r2_hidden(C_44, A_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.60/1.34  tff(c_143, plain, (![C_45]: (~r2_hidden(C_45, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_133])).
% 2.60/1.34  tff(c_153, plain, (![B_4]: (r1_xboole_0(k1_xboole_0, B_4))), inference(resolution, [status(thm)], [c_10, c_143])).
% 2.60/1.34  tff(c_299, plain, (![A_62, B_63, C_64, D_65]: (~r1_xboole_0(A_62, B_63) | r1_xboole_0(k2_zfmisc_1(A_62, C_64), k2_zfmisc_1(B_63, D_65)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.60/1.34  tff(c_24, plain, (![A_12]: (~r1_xboole_0(A_12, A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.60/1.34  tff(c_354, plain, (![B_67, D_68]: (k2_zfmisc_1(B_67, D_68)=k1_xboole_0 | ~r1_xboole_0(B_67, B_67))), inference(resolution, [status(thm)], [c_299, c_24])).
% 2.60/1.34  tff(c_371, plain, (![D_68]: (k2_zfmisc_1(k1_xboole_0, D_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_153, c_354])).
% 2.60/1.34  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.60/1.34  tff(c_38, plain, (r1_xboole_0(k1_relat_1('#skF_2'), k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.60/1.34  tff(c_79, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.34  tff(c_90, plain, (k3_xboole_0(k1_relat_1('#skF_2'), k1_relat_1('#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_79])).
% 2.60/1.34  tff(c_503, plain, (![A_85, B_86]: (r1_tarski(k1_relat_1(k3_xboole_0(A_85, B_86)), k3_xboole_0(k1_relat_1(A_85), k1_relat_1(B_86))) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.60/1.34  tff(c_517, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_2', '#skF_3')), k1_xboole_0) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_503])).
% 2.60/1.34  tff(c_525, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_2', '#skF_3')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_517])).
% 2.60/1.34  tff(c_20, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.60/1.34  tff(c_109, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(B_37, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.60/1.34  tff(c_118, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_109])).
% 2.60/1.34  tff(c_533, plain, (k1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_525, c_118])).
% 2.60/1.34  tff(c_34, plain, (![A_22]: (k3_xboole_0(A_22, k2_zfmisc_1(k1_relat_1(A_22), k2_relat_1(A_22)))=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.60/1.34  tff(c_551, plain, (k3_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k3_xboole_0('#skF_2', '#skF_3'))))=k3_xboole_0('#skF_2', '#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_533, c_34])).
% 2.60/1.34  tff(c_558, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0 | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_371, c_551])).
% 2.60/1.34  tff(c_559, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_78, c_558])).
% 2.60/1.34  tff(c_563, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_559])).
% 2.60/1.34  tff(c_567, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_563])).
% 2.60/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.34  
% 2.60/1.34  Inference rules
% 2.60/1.34  ----------------------
% 2.60/1.34  #Ref     : 0
% 2.60/1.34  #Sup     : 113
% 2.60/1.34  #Fact    : 0
% 2.60/1.34  #Define  : 0
% 2.60/1.34  #Split   : 1
% 2.60/1.34  #Chain   : 0
% 2.60/1.34  #Close   : 0
% 2.60/1.34  
% 2.60/1.34  Ordering : KBO
% 2.60/1.34  
% 2.60/1.34  Simplification rules
% 2.60/1.34  ----------------------
% 2.60/1.34  #Subsume      : 3
% 2.60/1.34  #Demod        : 60
% 2.60/1.34  #Tautology    : 61
% 2.60/1.34  #SimpNegUnit  : 4
% 2.60/1.34  #BackRed      : 3
% 2.60/1.34  
% 2.60/1.34  #Partial instantiations: 0
% 2.60/1.34  #Strategies tried      : 1
% 2.60/1.34  
% 2.60/1.34  Timing (in seconds)
% 2.60/1.34  ----------------------
% 2.60/1.35  Preprocessing        : 0.29
% 2.60/1.35  Parsing              : 0.16
% 2.60/1.35  CNF conversion       : 0.02
% 2.60/1.35  Main loop            : 0.29
% 2.60/1.35  Inferencing          : 0.11
% 2.60/1.35  Reduction            : 0.08
% 2.60/1.35  Demodulation         : 0.06
% 2.60/1.35  BG Simplification    : 0.01
% 2.60/1.35  Subsumption          : 0.06
% 2.60/1.35  Abstraction          : 0.01
% 2.60/1.35  MUC search           : 0.00
% 2.60/1.35  Cooper               : 0.00
% 2.60/1.35  Total                : 0.61
% 2.60/1.35  Index Insertion      : 0.00
% 2.60/1.35  Index Deletion       : 0.00
% 2.60/1.35  Index Matching       : 0.00
% 2.60/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
