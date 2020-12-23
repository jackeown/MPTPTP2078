%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:54 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 108 expanded)
%              Number of leaves         :   36 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :  107 ( 169 expanded)
%              Number of equality atoms :   41 (  52 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_50,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_86,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_67,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_69,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_75,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_54,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_121,plain,(
    ! [B_44,A_45] :
      ( v1_xboole_0(B_44)
      | ~ m1_subset_1(B_44,A_45)
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_137,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_121])).

tff(c_145,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_32,plain,(
    ! [B_17,A_16] :
      ( r2_hidden(B_17,A_16)
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_24,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_116,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_120,plain,(
    ! [A_11] : k3_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_116])).

tff(c_159,plain,(
    ! [A_52,B_53] : k5_xboole_0(A_52,k3_xboole_0(A_52,B_53)) = k4_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_168,plain,(
    ! [A_11] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_159])).

tff(c_172,plain,(
    ! [A_54] : k4_xboole_0(k1_xboole_0,A_54) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_168])).

tff(c_28,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_177,plain,(
    ! [A_54] : k5_xboole_0(A_54,k1_xboole_0) = k2_xboole_0(A_54,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_28])).

tff(c_181,plain,(
    ! [A_54] : k2_xboole_0(A_54,k1_xboole_0) = A_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_177])).

tff(c_56,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,(
    ! [A_27] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38,plain,(
    ! [A_18] : k1_subset_1(A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    ! [A_19] : k2_subset_1(A_19) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,(
    ! [A_22] : k3_subset_1(A_22,k1_subset_1(A_22)) = k2_subset_1(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_59,plain,(
    ! [A_22] : k3_subset_1(A_22,k1_subset_1(A_22)) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44])).

tff(c_60,plain,(
    ! [A_22] : k3_subset_1(A_22,k1_xboole_0) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_59])).

tff(c_569,plain,(
    ! [C_90,A_91,B_92] :
      ( r1_tarski(C_90,k3_subset_1(A_91,B_92))
      | ~ r1_tarski(B_92,k3_subset_1(A_91,C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(A_91))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_574,plain,(
    ! [C_90,A_91] :
      ( r1_tarski(C_90,k3_subset_1(A_91,k1_xboole_0))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(A_91))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_91)) ) ),
    inference(resolution,[status(thm)],[c_22,c_569])).

tff(c_580,plain,(
    ! [C_93,A_94] :
      ( r1_tarski(C_93,A_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(A_94)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_60,c_574])).

tff(c_592,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_580])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_598,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_592,c_20])).

tff(c_18,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_602,plain,(
    k5_xboole_0('#skF_2','#skF_2') = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_18])).

tff(c_605,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_602])).

tff(c_216,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k3_subset_1(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_228,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_216])).

tff(c_314,plain,(
    ! [A_62,B_63] : k2_xboole_0(k4_xboole_0(A_62,B_63),k4_xboole_0(B_63,A_62)) = k5_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_323,plain,(
    k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),k4_xboole_0('#skF_2','#skF_1')) = k5_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_314])).

tff(c_624,plain,(
    k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),k1_xboole_0) = k5_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_323])).

tff(c_625,plain,(
    k5_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_624])).

tff(c_16,plain,(
    ! [A_4,C_6,B_5] :
      ( r2_hidden(A_4,C_6)
      | ~ r2_hidden(A_4,B_5)
      | r2_hidden(A_4,k5_xboole_0(B_5,C_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_699,plain,(
    ! [A_99] :
      ( r2_hidden(A_99,'#skF_2')
      | ~ r2_hidden(A_99,'#skF_1')
      | r2_hidden(A_99,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_16])).

tff(c_50,plain,(
    ~ r2_hidden('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_708,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_699,c_50])).

tff(c_715,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_708])).

tff(c_718,plain,
    ( ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_715])).

tff(c_721,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_718])).

tff(c_723,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_721])).

tff(c_725,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_733,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_725,c_4])).

tff(c_737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_733])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:59:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.40  
% 2.72/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.41  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.72/1.41  
% 2.72/1.41  %Foreground sorts:
% 2.72/1.41  
% 2.72/1.41  
% 2.72/1.41  %Background operators:
% 2.72/1.41  
% 2.72/1.41  
% 2.72/1.41  %Foreground operators:
% 2.72/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.72/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.72/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.72/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.72/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.41  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.72/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.72/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.72/1.41  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.72/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.72/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.72/1.41  
% 2.72/1.42  tff(f_101, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 2.72/1.42  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.72/1.42  tff(f_48, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.72/1.42  tff(f_50, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.72/1.42  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.72/1.42  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.72/1.42  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.72/1.42  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.72/1.42  tff(f_86, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.72/1.42  tff(f_67, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.72/1.42  tff(f_69, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.72/1.42  tff(f_75, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.72/1.42  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 2.72/1.42  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.72/1.42  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.72/1.42  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.72/1.42  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.72/1.42  tff(c_58, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.72/1.42  tff(c_54, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.72/1.42  tff(c_121, plain, (![B_44, A_45]: (v1_xboole_0(B_44) | ~m1_subset_1(B_44, A_45) | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.72/1.42  tff(c_137, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_121])).
% 2.72/1.42  tff(c_145, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_137])).
% 2.72/1.42  tff(c_32, plain, (![B_17, A_16]: (r2_hidden(B_17, A_16) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.72/1.42  tff(c_52, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.72/1.42  tff(c_24, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.72/1.42  tff(c_26, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.72/1.42  tff(c_22, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.72/1.42  tff(c_116, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=A_42 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.72/1.42  tff(c_120, plain, (![A_11]: (k3_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_116])).
% 2.72/1.42  tff(c_159, plain, (![A_52, B_53]: (k5_xboole_0(A_52, k3_xboole_0(A_52, B_53))=k4_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.72/1.42  tff(c_168, plain, (![A_11]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_11))), inference(superposition, [status(thm), theory('equality')], [c_120, c_159])).
% 2.72/1.42  tff(c_172, plain, (![A_54]: (k4_xboole_0(k1_xboole_0, A_54)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_168])).
% 2.72/1.42  tff(c_28, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.72/1.42  tff(c_177, plain, (![A_54]: (k5_xboole_0(A_54, k1_xboole_0)=k2_xboole_0(A_54, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_172, c_28])).
% 2.72/1.42  tff(c_181, plain, (![A_54]: (k2_xboole_0(A_54, k1_xboole_0)=A_54)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_177])).
% 2.72/1.42  tff(c_56, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.72/1.42  tff(c_48, plain, (![A_27]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.72/1.42  tff(c_38, plain, (![A_18]: (k1_subset_1(A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.72/1.42  tff(c_40, plain, (![A_19]: (k2_subset_1(A_19)=A_19)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.72/1.42  tff(c_44, plain, (![A_22]: (k3_subset_1(A_22, k1_subset_1(A_22))=k2_subset_1(A_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.72/1.42  tff(c_59, plain, (![A_22]: (k3_subset_1(A_22, k1_subset_1(A_22))=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44])).
% 2.72/1.42  tff(c_60, plain, (![A_22]: (k3_subset_1(A_22, k1_xboole_0)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_59])).
% 2.72/1.42  tff(c_569, plain, (![C_90, A_91, B_92]: (r1_tarski(C_90, k3_subset_1(A_91, B_92)) | ~r1_tarski(B_92, k3_subset_1(A_91, C_90)) | ~m1_subset_1(C_90, k1_zfmisc_1(A_91)) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.72/1.42  tff(c_574, plain, (![C_90, A_91]: (r1_tarski(C_90, k3_subset_1(A_91, k1_xboole_0)) | ~m1_subset_1(C_90, k1_zfmisc_1(A_91)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_91)))), inference(resolution, [status(thm)], [c_22, c_569])).
% 2.72/1.42  tff(c_580, plain, (![C_93, A_94]: (r1_tarski(C_93, A_94) | ~m1_subset_1(C_93, k1_zfmisc_1(A_94)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_60, c_574])).
% 2.72/1.42  tff(c_592, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_580])).
% 2.72/1.42  tff(c_20, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.72/1.42  tff(c_598, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_592, c_20])).
% 2.72/1.42  tff(c_18, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.72/1.42  tff(c_602, plain, (k5_xboole_0('#skF_2', '#skF_2')=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_598, c_18])).
% 2.72/1.42  tff(c_605, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_602])).
% 2.72/1.42  tff(c_216, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k3_subset_1(A_58, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.72/1.42  tff(c_228, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_216])).
% 2.72/1.42  tff(c_314, plain, (![A_62, B_63]: (k2_xboole_0(k4_xboole_0(A_62, B_63), k4_xboole_0(B_63, A_62))=k5_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.42  tff(c_323, plain, (k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', '#skF_1'))=k5_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_228, c_314])).
% 2.72/1.42  tff(c_624, plain, (k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k1_xboole_0)=k5_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_605, c_323])).
% 2.72/1.42  tff(c_625, plain, (k5_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_624])).
% 2.72/1.42  tff(c_16, plain, (![A_4, C_6, B_5]: (r2_hidden(A_4, C_6) | ~r2_hidden(A_4, B_5) | r2_hidden(A_4, k5_xboole_0(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.72/1.42  tff(c_699, plain, (![A_99]: (r2_hidden(A_99, '#skF_2') | ~r2_hidden(A_99, '#skF_1') | r2_hidden(A_99, k3_subset_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_625, c_16])).
% 2.72/1.42  tff(c_50, plain, (~r2_hidden('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.72/1.42  tff(c_708, plain, (r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_699, c_50])).
% 2.72/1.42  tff(c_715, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_708])).
% 2.72/1.42  tff(c_718, plain, (~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_715])).
% 2.72/1.42  tff(c_721, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_718])).
% 2.72/1.42  tff(c_723, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_721])).
% 2.72/1.42  tff(c_725, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_137])).
% 2.72/1.42  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.42  tff(c_733, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_725, c_4])).
% 2.72/1.42  tff(c_737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_733])).
% 2.72/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.42  
% 2.72/1.42  Inference rules
% 2.72/1.42  ----------------------
% 2.72/1.42  #Ref     : 0
% 2.72/1.42  #Sup     : 164
% 2.72/1.42  #Fact    : 0
% 2.72/1.42  #Define  : 0
% 2.72/1.42  #Split   : 11
% 2.72/1.42  #Chain   : 0
% 2.72/1.42  #Close   : 0
% 2.72/1.42  
% 2.72/1.42  Ordering : KBO
% 2.72/1.42  
% 2.72/1.42  Simplification rules
% 2.72/1.42  ----------------------
% 2.72/1.42  #Subsume      : 14
% 2.72/1.42  #Demod        : 46
% 2.72/1.42  #Tautology    : 84
% 2.72/1.42  #SimpNegUnit  : 9
% 2.72/1.42  #BackRed      : 2
% 2.72/1.42  
% 2.72/1.42  #Partial instantiations: 0
% 2.72/1.42  #Strategies tried      : 1
% 2.72/1.42  
% 2.72/1.42  Timing (in seconds)
% 2.72/1.42  ----------------------
% 2.72/1.43  Preprocessing        : 0.32
% 2.72/1.43  Parsing              : 0.17
% 2.72/1.43  CNF conversion       : 0.02
% 2.72/1.43  Main loop            : 0.35
% 2.72/1.43  Inferencing          : 0.13
% 2.72/1.43  Reduction            : 0.11
% 2.72/1.43  Demodulation         : 0.07
% 2.72/1.43  BG Simplification    : 0.02
% 2.72/1.43  Subsumption          : 0.06
% 2.72/1.43  Abstraction          : 0.01
% 2.72/1.43  MUC search           : 0.00
% 2.72/1.43  Cooper               : 0.00
% 2.72/1.43  Total                : 0.70
% 2.72/1.43  Index Insertion      : 0.00
% 2.72/1.43  Index Deletion       : 0.00
% 2.72/1.43  Index Matching       : 0.00
% 2.72/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
