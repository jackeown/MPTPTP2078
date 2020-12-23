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
% DateTime   : Thu Dec  3 10:10:38 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 171 expanded)
%              Number of leaves         :   30 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  122 ( 332 expanded)
%              Number of equality atoms :   22 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_88,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ! [C] :
            ( r2_hidden(C,A)
           => r2_hidden(k4_tarski(C,C),B) )
       => r1_tarski(k6_relat_1(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_43,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_48,plain,(
    ! [A_25] : v1_relat_1(k1_wellord2(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_1'(A_14,B_15),A_14)
      | r1_tarski(k6_relat_1(A_14),B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [C_23,D_24,A_17] :
      ( r2_hidden(k4_tarski(C_23,D_24),k1_wellord2(A_17))
      | ~ r1_tarski(C_23,D_24)
      | ~ r2_hidden(D_24,A_17)
      | ~ r2_hidden(C_23,A_17)
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_54,plain,(
    ! [C_23,D_24,A_17] :
      ( r2_hidden(k4_tarski(C_23,D_24),k1_wellord2(A_17))
      | ~ r1_tarski(C_23,D_24)
      | ~ r2_hidden(D_24,A_17)
      | ~ r2_hidden(C_23,A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44])).

tff(c_608,plain,(
    ! [A_84,B_85] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_84,B_85),'#skF_1'(A_84,B_85)),B_85)
      | r1_tarski(k6_relat_1(A_84),B_85)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_612,plain,(
    ! [A_84,A_17] :
      ( r1_tarski(k6_relat_1(A_84),k1_wellord2(A_17))
      | ~ v1_relat_1(k1_wellord2(A_17))
      | ~ r1_tarski('#skF_1'(A_84,k1_wellord2(A_17)),'#skF_1'(A_84,k1_wellord2(A_17)))
      | ~ r2_hidden('#skF_1'(A_84,k1_wellord2(A_17)),A_17) ) ),
    inference(resolution,[status(thm)],[c_54,c_608])).

tff(c_616,plain,(
    ! [A_86,A_87] :
      ( r1_tarski(k6_relat_1(A_86),k1_wellord2(A_87))
      | ~ r2_hidden('#skF_1'(A_86,k1_wellord2(A_87)),A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_48,c_612])).

tff(c_620,plain,(
    ! [A_14] :
      ( r1_tarski(k6_relat_1(A_14),k1_wellord2(A_14))
      | ~ v1_relat_1(k1_wellord2(A_14)) ) ),
    inference(resolution,[status(thm)],[c_28,c_616])).

tff(c_624,plain,(
    ! [A_88] : r1_tarski(k6_relat_1(A_88),k1_wellord2(A_88)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_620])).

tff(c_14,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_329,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(k1_relat_1(A_54),k1_relat_1(B_55))
      | ~ r1_tarski(A_54,B_55)
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_337,plain,(
    ! [A_13,B_55] :
      ( r1_tarski(A_13,k1_relat_1(B_55))
      | ~ r1_tarski(k6_relat_1(A_13),B_55)
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_329])).

tff(c_344,plain,(
    ! [A_13,B_55] :
      ( r1_tarski(A_13,k1_relat_1(B_55))
      | ~ r1_tarski(k6_relat_1(A_13),B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_337])).

tff(c_630,plain,(
    ! [A_88] :
      ( r1_tarski(A_88,k1_relat_1(k1_wellord2(A_88)))
      | ~ v1_relat_1(k1_wellord2(A_88)) ) ),
    inference(resolution,[status(thm)],[c_624,c_344])).

tff(c_641,plain,(
    ! [A_88] : r1_tarski(A_88,k1_relat_1(k1_wellord2(A_88))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_630])).

tff(c_42,plain,(
    ! [A_17] :
      ( k3_relat_1(k1_wellord2(A_17)) = A_17
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_56,plain,(
    ! [A_17] : k3_relat_1(k1_wellord2(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42])).

tff(c_146,plain,(
    ! [A_41] :
      ( k2_xboole_0(k1_relat_1(A_41),k2_relat_1(A_41)) = k3_relat_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_208,plain,(
    ! [A_45] :
      ( r1_tarski(k1_relat_1(A_45),k3_relat_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_10])).

tff(c_222,plain,(
    ! [A_17] :
      ( r1_tarski(k1_relat_1(k1_wellord2(A_17)),A_17)
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_208])).

tff(c_232,plain,(
    ! [A_48] : r1_tarski(k1_relat_1(k1_wellord2(A_48)),A_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_222])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_238,plain,(
    ! [A_48] :
      ( k1_relat_1(k1_wellord2(A_48)) = A_48
      | ~ r1_tarski(A_48,k1_relat_1(k1_wellord2(A_48))) ) ),
    inference(resolution,[status(thm)],[c_232,c_2])).

tff(c_663,plain,(
    ! [A_48] : k1_relat_1(k1_wellord2(A_48)) = A_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_238])).

tff(c_690,plain,(
    ! [A_91] : k1_relat_1(k1_wellord2(A_91)) = A_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_238])).

tff(c_12,plain,(
    ! [A_7] :
      ( k2_xboole_0(k1_relat_1(A_7),k2_relat_1(A_7)) = k3_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_717,plain,(
    ! [A_91] :
      ( k2_xboole_0(A_91,k2_relat_1(k1_wellord2(A_91))) = k3_relat_1(k1_wellord2(A_91))
      | ~ v1_relat_1(k1_wellord2(A_91)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_12])).

tff(c_737,plain,(
    ! [A_91] : k2_xboole_0(A_91,k2_relat_1(k1_wellord2(A_91))) = A_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_56,c_717])).

tff(c_24,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_379,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k2_relat_1(A_59),k2_relat_1(B_60))
      | ~ r1_tarski(A_59,B_60)
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_387,plain,(
    ! [A_13,B_60] :
      ( r1_tarski(A_13,k2_relat_1(B_60))
      | ~ r1_tarski(k6_relat_1(A_13),B_60)
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_379])).

tff(c_394,plain,(
    ! [A_13,B_60] :
      ( r1_tarski(A_13,k2_relat_1(B_60))
      | ~ r1_tarski(k6_relat_1(A_13),B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_387])).

tff(c_627,plain,(
    ! [A_88] :
      ( r1_tarski(A_88,k2_relat_1(k1_wellord2(A_88)))
      | ~ v1_relat_1(k1_wellord2(A_88)) ) ),
    inference(resolution,[status(thm)],[c_624,c_394])).

tff(c_644,plain,(
    ! [A_89] : r1_tarski(A_89,k2_relat_1(k1_wellord2(A_89))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_627])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_661,plain,(
    ! [A_89] : k2_xboole_0(A_89,k2_relat_1(k1_wellord2(A_89))) = k2_relat_1(k1_wellord2(A_89)) ),
    inference(resolution,[status(thm)],[c_644,c_8])).

tff(c_821,plain,(
    ! [A_98] : k2_relat_1(k1_wellord2(A_98)) = A_98 ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_661])).

tff(c_16,plain,(
    ! [A_9] :
      ( r1_tarski(A_9,k2_zfmisc_1(k1_relat_1(A_9),k2_relat_1(A_9)))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_836,plain,(
    ! [A_98] :
      ( r1_tarski(k1_wellord2(A_98),k2_zfmisc_1(k1_relat_1(k1_wellord2(A_98)),A_98))
      | ~ v1_relat_1(k1_wellord2(A_98)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_16])).

tff(c_851,plain,(
    ! [A_98] : r1_tarski(k1_wellord2(A_98),k2_zfmisc_1(A_98,A_98)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_663,c_836])).

tff(c_50,plain,(
    ~ r1_tarski(k1_wellord2('#skF_4'),k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_857,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_851,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.46  
% 2.90/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.46  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.90/1.46  
% 2.90/1.46  %Foreground sorts:
% 2.90/1.46  
% 2.90/1.46  
% 2.90/1.46  %Background operators:
% 2.90/1.46  
% 2.90/1.46  
% 2.90/1.46  %Foreground operators:
% 2.90/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.90/1.46  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.90/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.90/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.90/1.46  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.90/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.90/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.90/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.90/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.90/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.90/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.90/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.90/1.46  
% 2.90/1.48  tff(f_88, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.90/1.48  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => ((![C]: (r2_hidden(C, A) => r2_hidden(k4_tarski(C, C), B))) => r1_tarski(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_relat_1)).
% 2.90/1.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.90/1.48  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 2.90/1.48  tff(f_43, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.90/1.48  tff(f_62, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.90/1.48  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.90/1.48  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.90/1.48  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.90/1.48  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.90/1.48  tff(f_47, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.90/1.48  tff(f_91, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 2.90/1.48  tff(c_48, plain, (![A_25]: (v1_relat_1(k1_wellord2(A_25)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.90/1.48  tff(c_28, plain, (![A_14, B_15]: (r2_hidden('#skF_1'(A_14, B_15), A_14) | r1_tarski(k6_relat_1(A_14), B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.90/1.48  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.90/1.48  tff(c_44, plain, (![C_23, D_24, A_17]: (r2_hidden(k4_tarski(C_23, D_24), k1_wellord2(A_17)) | ~r1_tarski(C_23, D_24) | ~r2_hidden(D_24, A_17) | ~r2_hidden(C_23, A_17) | ~v1_relat_1(k1_wellord2(A_17)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.90/1.48  tff(c_54, plain, (![C_23, D_24, A_17]: (r2_hidden(k4_tarski(C_23, D_24), k1_wellord2(A_17)) | ~r1_tarski(C_23, D_24) | ~r2_hidden(D_24, A_17) | ~r2_hidden(C_23, A_17))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44])).
% 2.90/1.48  tff(c_608, plain, (![A_84, B_85]: (~r2_hidden(k4_tarski('#skF_1'(A_84, B_85), '#skF_1'(A_84, B_85)), B_85) | r1_tarski(k6_relat_1(A_84), B_85) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.90/1.48  tff(c_612, plain, (![A_84, A_17]: (r1_tarski(k6_relat_1(A_84), k1_wellord2(A_17)) | ~v1_relat_1(k1_wellord2(A_17)) | ~r1_tarski('#skF_1'(A_84, k1_wellord2(A_17)), '#skF_1'(A_84, k1_wellord2(A_17))) | ~r2_hidden('#skF_1'(A_84, k1_wellord2(A_17)), A_17))), inference(resolution, [status(thm)], [c_54, c_608])).
% 2.90/1.48  tff(c_616, plain, (![A_86, A_87]: (r1_tarski(k6_relat_1(A_86), k1_wellord2(A_87)) | ~r2_hidden('#skF_1'(A_86, k1_wellord2(A_87)), A_87))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_48, c_612])).
% 2.90/1.48  tff(c_620, plain, (![A_14]: (r1_tarski(k6_relat_1(A_14), k1_wellord2(A_14)) | ~v1_relat_1(k1_wellord2(A_14)))), inference(resolution, [status(thm)], [c_28, c_616])).
% 2.90/1.48  tff(c_624, plain, (![A_88]: (r1_tarski(k6_relat_1(A_88), k1_wellord2(A_88)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_620])).
% 2.90/1.48  tff(c_14, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.90/1.48  tff(c_22, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.90/1.48  tff(c_329, plain, (![A_54, B_55]: (r1_tarski(k1_relat_1(A_54), k1_relat_1(B_55)) | ~r1_tarski(A_54, B_55) | ~v1_relat_1(B_55) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.90/1.48  tff(c_337, plain, (![A_13, B_55]: (r1_tarski(A_13, k1_relat_1(B_55)) | ~r1_tarski(k6_relat_1(A_13), B_55) | ~v1_relat_1(B_55) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_329])).
% 2.90/1.48  tff(c_344, plain, (![A_13, B_55]: (r1_tarski(A_13, k1_relat_1(B_55)) | ~r1_tarski(k6_relat_1(A_13), B_55) | ~v1_relat_1(B_55))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_337])).
% 2.90/1.48  tff(c_630, plain, (![A_88]: (r1_tarski(A_88, k1_relat_1(k1_wellord2(A_88))) | ~v1_relat_1(k1_wellord2(A_88)))), inference(resolution, [status(thm)], [c_624, c_344])).
% 2.90/1.48  tff(c_641, plain, (![A_88]: (r1_tarski(A_88, k1_relat_1(k1_wellord2(A_88))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_630])).
% 2.90/1.48  tff(c_42, plain, (![A_17]: (k3_relat_1(k1_wellord2(A_17))=A_17 | ~v1_relat_1(k1_wellord2(A_17)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.90/1.48  tff(c_56, plain, (![A_17]: (k3_relat_1(k1_wellord2(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42])).
% 2.90/1.48  tff(c_146, plain, (![A_41]: (k2_xboole_0(k1_relat_1(A_41), k2_relat_1(A_41))=k3_relat_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.90/1.48  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.90/1.48  tff(c_208, plain, (![A_45]: (r1_tarski(k1_relat_1(A_45), k3_relat_1(A_45)) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_146, c_10])).
% 2.90/1.48  tff(c_222, plain, (![A_17]: (r1_tarski(k1_relat_1(k1_wellord2(A_17)), A_17) | ~v1_relat_1(k1_wellord2(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_208])).
% 2.90/1.48  tff(c_232, plain, (![A_48]: (r1_tarski(k1_relat_1(k1_wellord2(A_48)), A_48))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_222])).
% 2.90/1.48  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.90/1.48  tff(c_238, plain, (![A_48]: (k1_relat_1(k1_wellord2(A_48))=A_48 | ~r1_tarski(A_48, k1_relat_1(k1_wellord2(A_48))))), inference(resolution, [status(thm)], [c_232, c_2])).
% 2.90/1.48  tff(c_663, plain, (![A_48]: (k1_relat_1(k1_wellord2(A_48))=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_641, c_238])).
% 2.90/1.48  tff(c_690, plain, (![A_91]: (k1_relat_1(k1_wellord2(A_91))=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_641, c_238])).
% 2.90/1.48  tff(c_12, plain, (![A_7]: (k2_xboole_0(k1_relat_1(A_7), k2_relat_1(A_7))=k3_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.90/1.48  tff(c_717, plain, (![A_91]: (k2_xboole_0(A_91, k2_relat_1(k1_wellord2(A_91)))=k3_relat_1(k1_wellord2(A_91)) | ~v1_relat_1(k1_wellord2(A_91)))), inference(superposition, [status(thm), theory('equality')], [c_690, c_12])).
% 2.90/1.48  tff(c_737, plain, (![A_91]: (k2_xboole_0(A_91, k2_relat_1(k1_wellord2(A_91)))=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_56, c_717])).
% 2.90/1.48  tff(c_24, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.90/1.48  tff(c_379, plain, (![A_59, B_60]: (r1_tarski(k2_relat_1(A_59), k2_relat_1(B_60)) | ~r1_tarski(A_59, B_60) | ~v1_relat_1(B_60) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.90/1.48  tff(c_387, plain, (![A_13, B_60]: (r1_tarski(A_13, k2_relat_1(B_60)) | ~r1_tarski(k6_relat_1(A_13), B_60) | ~v1_relat_1(B_60) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_379])).
% 2.90/1.48  tff(c_394, plain, (![A_13, B_60]: (r1_tarski(A_13, k2_relat_1(B_60)) | ~r1_tarski(k6_relat_1(A_13), B_60) | ~v1_relat_1(B_60))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_387])).
% 2.90/1.48  tff(c_627, plain, (![A_88]: (r1_tarski(A_88, k2_relat_1(k1_wellord2(A_88))) | ~v1_relat_1(k1_wellord2(A_88)))), inference(resolution, [status(thm)], [c_624, c_394])).
% 2.90/1.48  tff(c_644, plain, (![A_89]: (r1_tarski(A_89, k2_relat_1(k1_wellord2(A_89))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_627])).
% 2.90/1.48  tff(c_8, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.90/1.48  tff(c_661, plain, (![A_89]: (k2_xboole_0(A_89, k2_relat_1(k1_wellord2(A_89)))=k2_relat_1(k1_wellord2(A_89)))), inference(resolution, [status(thm)], [c_644, c_8])).
% 2.90/1.48  tff(c_821, plain, (![A_98]: (k2_relat_1(k1_wellord2(A_98))=A_98)), inference(demodulation, [status(thm), theory('equality')], [c_737, c_661])).
% 2.90/1.48  tff(c_16, plain, (![A_9]: (r1_tarski(A_9, k2_zfmisc_1(k1_relat_1(A_9), k2_relat_1(A_9))) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.90/1.48  tff(c_836, plain, (![A_98]: (r1_tarski(k1_wellord2(A_98), k2_zfmisc_1(k1_relat_1(k1_wellord2(A_98)), A_98)) | ~v1_relat_1(k1_wellord2(A_98)))), inference(superposition, [status(thm), theory('equality')], [c_821, c_16])).
% 2.90/1.48  tff(c_851, plain, (![A_98]: (r1_tarski(k1_wellord2(A_98), k2_zfmisc_1(A_98, A_98)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_663, c_836])).
% 2.90/1.48  tff(c_50, plain, (~r1_tarski(k1_wellord2('#skF_4'), k2_zfmisc_1('#skF_4', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.90/1.48  tff(c_857, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_851, c_50])).
% 2.90/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.48  
% 2.90/1.48  Inference rules
% 2.90/1.48  ----------------------
% 2.90/1.48  #Ref     : 0
% 2.90/1.48  #Sup     : 161
% 2.90/1.48  #Fact    : 0
% 2.90/1.48  #Define  : 0
% 2.90/1.48  #Split   : 0
% 2.90/1.48  #Chain   : 0
% 2.90/1.48  #Close   : 0
% 2.90/1.48  
% 2.90/1.48  Ordering : KBO
% 2.90/1.48  
% 2.90/1.48  Simplification rules
% 2.90/1.48  ----------------------
% 2.90/1.48  #Subsume      : 9
% 2.90/1.48  #Demod        : 202
% 2.90/1.48  #Tautology    : 80
% 2.90/1.48  #SimpNegUnit  : 0
% 2.90/1.48  #BackRed      : 7
% 2.90/1.48  
% 2.90/1.48  #Partial instantiations: 0
% 2.90/1.48  #Strategies tried      : 1
% 2.90/1.48  
% 2.90/1.48  Timing (in seconds)
% 2.90/1.48  ----------------------
% 2.90/1.48  Preprocessing        : 0.32
% 2.90/1.48  Parsing              : 0.17
% 2.90/1.48  CNF conversion       : 0.02
% 2.90/1.48  Main loop            : 0.33
% 2.90/1.48  Inferencing          : 0.12
% 2.90/1.48  Reduction            : 0.11
% 2.90/1.48  Demodulation         : 0.08
% 2.90/1.48  BG Simplification    : 0.02
% 2.90/1.48  Subsumption          : 0.06
% 2.90/1.48  Abstraction          : 0.02
% 2.90/1.48  MUC search           : 0.00
% 2.90/1.48  Cooper               : 0.00
% 2.90/1.48  Total                : 0.68
% 2.90/1.48  Index Insertion      : 0.00
% 2.90/1.48  Index Deletion       : 0.00
% 2.90/1.48  Index Matching       : 0.00
% 2.90/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
